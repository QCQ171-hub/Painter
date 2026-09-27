// ============================================================================
//  ColorPick —— 图片颜色提取 / 连通块框选工具
//  纯 Win32 + GDI+ 实现，无第三方依赖（MinGW-w64 编译）
//
//  功能
//   1. 打开（上传）一张图片：左侧按钮 / 按 O / 直接把图片拖进窗口
//   2. 左侧色卡列出图中出现过的【全部】颜色，按 RGB 三通道均值从小到大排序
//   3. 点击色卡中的某个颜色：
//        - 其十六进制色号复制到剪贴板
//        - 沿图中所有该颜色像素的实际形状描出轮廓（相连像素作为一个整体，
//          轮廓按像素边走线并闭合成多边形，不是矩形外接框）
//   4. 空格切换到下一个颜色（Shift+空格 上一个），列表自动滚动跟随
//   5. 点击（或在图中拖动）任意一个像素：底栏右侧显示它的位置。位置按该像素
//      所在的四分区域，从最近的边缘计数（1 基）——
//        左上区域 => 「左起第 x 个 · 上起第 y 个」
//        右上区域 => 「右起第 x 个 · 上起第 y 个」
//        左下区域 => 「左起第 x 个 · 下起第 y 个」
//        右下区域 => 「右起第 x 个 · 下起第 y 个」
//      同时在图上画十字准线 + 选中框标出该像素，并给出其色号。按 Esc 清除。
//
//  命令行自检模式（无界面，便于自动化验证）：
//   colorpick.exe --selftest <输入图> <输出叠加图.png> <输出日志.txt> [色卡下标|#RRGGBB]
// ============================================================================

#ifndef UNICODE
#define UNICODE
#endif
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX

#include <windows.h>
#include <windowsx.h>
#include <shellapi.h>
#include <commdlg.h>
#include <objbase.h>

#include <gdiplus.h>

#include <cstdio>
#include <cstdarg>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <unordered_map>
#include <algorithm>

using namespace Gdiplus;

// ----------------------------------------------------------------------------
// 常量 / 布局
// ----------------------------------------------------------------------------
static const int  PALETTE_W  = 172;   // 左侧色卡面板宽度
static const int  HEADER_H   = 62;    // 色卡顶部区域（按钮 + 统计）
static const int  ITEM_H     = 26;    // 单个色卡条目高度
static const int  SWATCH     = 18;    // 色块边长
static const int  STATUS_H   = 26;    // 底部状态栏高度
static const int  MAX_COMPS  = 8000;  // 最多处理的连通块数量（防止极端噪点图卡顿）

// ----------------------------------------------------------------------------
// 全局状态
// ----------------------------------------------------------------------------
static ULONG_PTR     g_gdipToken = 0;
static HWND          g_hwnd      = NULL;
static HINSTANCE     g_hInst     = NULL;
static FontFamily*   g_ff        = NULL;
static Font*         g_font      = NULL;   // 12px
static Font*         g_fontSm    = NULL;   // 11px

static Bitmap*       g_bmp       = NULL;   // 显示用位图（32bppRGB）
static int           g_w = 0, g_h = 0;     // 图像尺寸
static std::vector<uint32_t> g_px;         // 像素，0x00RRGGBB，行优先
static std::vector<int>      g_inMask;     // 连通块访问标记（时间戳）
static int           g_stamp = 0;

struct ColorInfo { uint32_t rgb; int cnt; };
static std::vector<ColorInfo> g_pal;       // 已按三通道均值升序排序
static int           g_sel    = -1;        // 当前选中色卡下标
static int           g_scroll = 0;         // 色卡滚动像素

// 连通块：保存实际形状。轮廓为像素边界网格上的闭合多边形（可多条：外轮廓 + 洞），
// 点用 int2 表示网格点 (px,py)，按像素边描线 => 形状是什么样就框成什么样。
struct Contour {
    int area;                       // 像素数
    int x0, y0, x1, y1;             // 外接范围（网格点坐标，供校验）
    std::vector<int> xs, ys;        // 所有环展平；新环以下一个环起点重新开始
    std::vector<int> ringStart;     // 每个环在 xs/ys 中的起始下标（环尾不重复起点）
};
static std::vector<Contour> g_comps;       // 选中颜色的连通块（图像坐标）
static bool            g_truncated = false;
static wchar_t         g_status[256] = L"";
static std::wstring    g_path;
static FILE*           g_logf = NULL;

// 像素拾取（点击/拖动查看位置）
static int             g_pickX = -1, g_pickY = -1;  // 选中像素（0 基），-1 = 无
static bool            g_pickDrag = false;          // 左键拖动连续拾取中
static wchar_t         g_pickText[160] = L"";       // 底栏右侧位置文本
// 当前视口变换（paint 时更新，供命中测试反算图像坐标）
static double          g_viewS = 1.0, g_viewOx = 0.0, g_viewOy = 0.0;
static bool            g_viewReady = false;

// 视口矩形（客户区坐标）
static RECT g_rcImage = {0,0,0,0};
static RECT g_rcList  = {0,0,0,0};
static RECT g_rcBtn   = {0,0,0,0};

static inline bool hit(const RECT& r, int x, int y) {
    return x >= r.left && x < r.right && y >= r.top && y < r.bottom;
}

// ----------------------------------------------------------------------------
// 小工具
// ----------------------------------------------------------------------------
static std::wstring hexOf(uint32_t c) {
    wchar_t b[16];
    swprintf(b, 16, L"#%02X%02X%02X", (unsigned)((c >> 16) & 255),
             (unsigned)((c >> 8) & 255), (unsigned)(c & 255));
    return b;
}

static bool parseHex(const wchar_t* s, uint32_t& out) {
    if (!s || !*s) return false;
    if (*s == L'#') ++s;
    if (wcslen(s) < 2) return false;
    wchar_t* end = NULL;
    unsigned long v = wcstoul(s, &end, 16);
    if (end == s) return false;
    out = (uint32_t)v & 0xFFFFFFu;
    return true;
}

// 三通道之和 —— 与三通道均值完全同序，用整数避免浮点误差
static inline uint64_t chanSum(uint32_t c) {
    return ((c >> 16) & 255) + ((c >> 8) & 255) + (c & 255);
}

static void say(const char* fmt, ...) {
    char buf[1024];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    fputs(buf, stderr);
    fflush(stderr);
    if (g_logf) { fputs(buf, g_logf); fflush(g_logf); }
}

// ----------------------------------------------------------------------------
// 图像载入：解码 + 抽像素 + 建色卡
// ----------------------------------------------------------------------------
static void clearSelection() {
    g_sel = -1;
    g_comps.clear();
    g_truncated = false;
    g_status[0] = 0;
    g_scroll = 0;
}

// 窗口标题：ColorPick - 文件名（未载入时仅 ColorPick）
static void applyWindowTitle() {
    if (!g_hwnd) return;
    std::wstring title = L"ColorPick";
    if (!g_path.empty()) {
        size_t pos = g_path.find_last_of(L"\\/");
        title += L" - ";
        title += (pos == std::wstring::npos) ? g_path : g_path.substr(pos + 1);
    }
    SetWindowTextW(g_hwnd, title.c_str());
}

static void buildPalette() {
    g_pal.clear();
    std::unordered_map<uint32_t, int> cnt;
    const size_t n = g_px.size();
    cnt.reserve(n < 4096u ? 128u : n / 8u);
    for (size_t i = 0; i < n; ++i) ++cnt[g_px[i]];
    g_pal.reserve(cnt.size());
    for (std::unordered_map<uint32_t, int>::iterator it = cnt.begin(); it != cnt.end(); ++it)
        g_pal.push_back({ it->first, it->second });

    // 排序：三通道均值（=通道和/3）升序；同均值时次数多的在前，再按色号升序
    std::sort(g_pal.begin(), g_pal.end(), [](const ColorInfo& a, const ColorInfo& b) {
        uint64_t sa = chanSum(a.rgb), sb = chanSum(b.rgb);
        if (sa != sb) return sa < sb;
        if (a.cnt != b.cnt) return a.cnt > b.cnt;
        return a.rgb < b.rgb;
    });
}

static Bitmap* loadBitmapFrom(const wchar_t* path, int& W, int& H, std::vector<uint32_t>& px) {
    W = H = 0;
    Bitmap* raw = Bitmap::FromFile(path, FALSE);
    if (!raw || raw->GetLastStatus() != Ok || !raw->GetWidth() || !raw->GetHeight()) {
        delete raw; return NULL;
    }
    const int nw = (int)raw->GetWidth(), nh = (int)raw->GetHeight();
    if ((long long)nw * (long long)nh > 60000000LL) { delete raw; return NULL; }

    // 统一转成 32bppRGB 后再读像素，保证 PNG/JPG/BMP/GIF/TIFF 等格式行为一致
    Bitmap* conv = new Bitmap(nw, nh, PixelFormat32bppRGB);
    if (conv->GetLastStatus() != Ok) { delete conv; delete raw; return NULL; }
    {
        Graphics gg(conv);
        gg.SetInterpolationMode(InterpolationModeNearestNeighbor);
        gg.DrawImage(raw, Rect(0, 0, nw, nh), 0, 0, nw, nh, UnitPixel);
    }

    BitmapData bd;
    Rect full(0, 0, nw, nh);
    if (conv->LockBits(&full, ImageLockModeRead, PixelFormat32bppRGB, &bd) != Ok) {
        delete conv; delete raw; return NULL;
    }
    px.assign((size_t)nw * nh, 0);
    const byte* base = (const byte*)bd.Scan0;
    for (int y = 0; y < nh; ++y) {
        const uint32_t* row = (const uint32_t*)(base + (ptrdiff_t)y * bd.Stride);
        uint32_t* dst = &px[(size_t)y * nw];
        for (int x = 0; x < nw; ++x) dst[x] = row[x] & 0xFFFFFFu;   // 丢弃 alpha
    }
    conv->UnlockBits(&bd);

    delete raw;
    W = nw; H = nh;
    return conv;   // 直接用作显示位图
}

static void refreshScrollBar() {
    if (!g_hwnd) return;
    SCROLLINFO si = { sizeof(si), SIF_RANGE | SIF_PAGE | SIF_POS };
    const int listH = (int)(g_rcList.bottom - g_rcList.top);
    si.nMax  = g_pal.empty() ? 0 : (int)g_pal.size() - 1;
    si.nPage = std::max(1, listH / ITEM_H);
    si.nPos  = g_scroll / ITEM_H;
    SetScrollInfo(g_hwnd, SB_VERT, &si, TRUE);
}

static bool openImage(const wchar_t* path) {
    int W = 0, H = 0;
    std::vector<uint32_t> px;
    Bitmap* b = loadBitmapFrom(path, W, H, px);
    if (!b) return false;

    delete g_bmp;
    g_bmp = b; g_w = W; g_h = H; g_px = std::move(px);
    g_inMask.assign((size_t)W * H, 0);
    g_stamp = 0;
    buildPalette();
    clearSelection();
    g_pickX = g_pickY = -1;
    g_pickText[0] = 0;
    g_viewReady = false;
    g_path = path;
    applyWindowTitle();

    swprintf(g_status, 256,
             L"已载入 %d×%d · 唯一颜色 %d 种 · 点击色卡或按空格切换",
             g_w, g_h, (int)g_pal.size());
    refreshScrollBar();
    InvalidateRect(g_hwnd, NULL, FALSE);
    return true;
}

// ----------------------------------------------------------------------------
// 连通块：4 邻域泛洪 + 像素边轮廓追踪，得到每个连通区域的实际形状轮廓
//
// 轮廓在 (W+1)x(H+1) 的像素边界网格上走线：一条“边”是颜色像素与非该颜色像素
// （或图像外）的共享边。外轮廓按右转优先闭合，洞轮廓按左转优先闭合，
// 因此形状是什么样就描成什么样（阶梯状沿像素边走），而不是矩形外接框。
// ----------------------------------------------------------------------------
static inline uint64_t edgeKey(int gx, int gy, int dir) {
    return ((uint64_t)(uint32_t)gx << 34) | ((uint64_t)(uint32_t)gy << 2) | (uint64_t)dir;
}
static const int DX[4] = { 1, 0, -1, 0 };
static const int DY[4] = { 0, 1, 0, -1 };   // 0=右 1=下 2=左 3=上

// 从有向边 (sx,sy,sdir) 出发沿轮廓走一圈；边走过的有向边从集合中删除。
// 优先“右转”，可让外轮廓闭合，剩余边自然成为洞轮廓。
static void traceRings(std::unordered_map<uint64_t, char>& edges,
                       std::vector<int>& xs, std::vector<int>& ys,
                       std::vector<int>& ringStart,
                       int sx, int sy, int sdir) {
    int gx = sx, gy = sy, dir = sdir;
    ringStart.push_back((int)xs.size());
    xs.push_back(gx); ys.push_back(gy);

    // 环约定：起点不在尾部重复出现。所有退出路径统一走这里收尾。
    struct Finish {
        std::vector<int>& xs; std::vector<int>& ys;
        const std::vector<int>& ringStart;
        ~Finish() {
            const int s0 = ringStart.back();
            if ((int)xs.size() - s0 >= 2 && xs.back() == xs[s0] && ys.back() == ys[s0]) {
                xs.pop_back();
                ys.pop_back();
            }
        }
    } finish = { xs, ys, ringStart };

    const int guardLimit = (int)edges.size() + 8;
    for (int guard = 0; guard < guardLimit; ++guard) {
        const uint64_t k = edgeKey(gx, gy, dir);
        std::unordered_map<uint64_t, char>::iterator it = edges.find(k);
        if (it == edges.end()) return;        // 该有向边已被走过，环结束
        edges.erase(it);

        gx += DX[dir];
        gy += DY[dir];
        xs.push_back(gx); ys.push_back(gy);

        // 下一个方向：右转优先，其次直行、左转、掉头
        const int order[4] = { (dir + 1) & 3, dir, (dir + 3) & 3, (dir + 2) & 3 };
        bool moved = false;
        for (int t = 0; t < 4; ++t) {
            const int nd = order[t];
            if (edges.count(edgeKey(gx, gy, nd))) { dir = nd; moved = true; break; }
        }
        if (!moved) return;                   // 死路，环收尾
    }
}

static void computeContours(uint32_t color) {
    g_comps.clear();
    g_truncated = false;
    if (g_w <= 0 || g_h <= 0) return;

    const int W = g_w, H = g_h;
    const size_t N = (size_t)W * H;
    if (g_inMask.size() != N) { g_inMask.assign(N, 0); g_stamp = 0; }
    ++g_stamp;
    const int stamp = g_stamp;
    const uint32_t* px = g_px.data();
    int* inMask = g_inMask.data();

    std::vector<int> stk;
    stk.reserve(4096);

    // 全图一次性标记该颜色的像素归属（逐块处理时再清）
    for (int y = 0; y < H && !g_truncated; ++y) {
        const int rowbase = y * W;
        for (int x = 0; x < W; ++x) {
            const int i0 = rowbase + x;
            if (px[i0] != color || inMask[i0] == stamp) continue;

            // ---- 泛洪收集本连通块 ----
            stk.clear();
            stk.push_back(i0);
            inMask[i0] = stamp;
            int minx = x, maxx = x, miny = y, maxy = y, area = 0;
            std::vector<int> compPix;
            compPix.reserve(256);

            while (!stk.empty()) {
                const int i = stk.back();
                stk.pop_back();
                const int cx = i % W, cy = i / W;
                ++area;
                compPix.push_back(i);
                if (cx < minx) minx = cx;
                if (cx > maxx) maxx = cx;
                if (cy < miny) miny = cy;
                if (cy > maxy) maxy = cy;

                if (cx > 0)     { const int j = i - 1; if (px[j] == color && inMask[j] != stamp) { inMask[j] = stamp; stk.push_back(j); } }
                if (cx + 1 < W) { const int j = i + 1; if (px[j] == color && inMask[j] != stamp) { inMask[j] = stamp; stk.push_back(j); } }
                if (cy > 0)     { const int j = i - W; if (px[j] == color && inMask[j] != stamp) { inMask[j] = stamp; stk.push_back(j); } }
                if (cy + 1 < H) { const int j = i + W; if (px[j] == color && inMask[j] != stamp) { inMask[j] = stamp; stk.push_back(j); } }
            }

            if ((int)g_comps.size() >= MAX_COMPS) { g_truncated = true; break; }

            // ---- 收集本块的像素边界边（有向：使颜色在边的左侧） ----
            std::unordered_map<uint64_t, char> edges;
            edges.reserve(compPix.size() * 4);
            auto isColor = [&](int cx, int cy) -> bool {
                if (cx < 0 || cy < 0 || cx >= W || cy >= H) return false;
                return px[(size_t)cy * W + cx] == color;
            };
            int startEx = -1, startEy = -1;                 // 最上最左像素的顶边 = 外轮廓起点
            for (size_t t = 0; t < compPix.size(); ++t) {
                const int i = compPix[t];
                const int cx = i % W, cy = i / W;
                // 上边：从 (cx,cy) 向右，当上方不是该颜色
                if (!isColor(cx, cy - 1)) {
                    edges[edgeKey(cx, cy, 0)] = 1;
                    if (startEx < 0 || cy < startEy || (cy == startEy && cx < startEx)) { startEx = cx; startEy = cy; }
                }
                // 右边：从 (cx+1,cy) 向下
                if (!isColor(cx + 1, cy)) edges[edgeKey(cx + 1, cy, 1)] = 1;
                // 下边：从 (cx+1,cy+1) 向左
                if (!isColor(cx, cy + 1)) edges[edgeKey(cx + 1, cy + 1, 2)] = 1;
                // 左边：从 (cx,cy+1) 向上
                if (!isColor(cx - 1, cy)) edges[edgeKey(cx, cy + 1, 3)] = 1;
            }

            Contour c;
            c.area = area;
            c.x0 = minx; c.y0 = miny; c.x1 = maxx; c.y1 = maxy;
            if (!edges.empty() && startEx >= 0)
                traceRings(edges, c.xs, c.ys, c.ringStart, startEx, startEy, 0);
            // 剩余边 → 洞轮廓（各自闭合成环）
            while (!edges.empty()) {
                const uint64_t k = edges.begin()->first;
                const int egx = (int)(uint32_t)(k >> 34);
                const int egy = (int)(uint32_t)((k >> 2) & 0xFFFFFFFFu);
                const int edir = (int)(k & 3);
                traceRings(edges, c.xs, c.ys, c.ringStart, egx, egy, edir);
            }
            g_comps.push_back(std::move(c));
        }
    }
}

// ----------------------------------------------------------------------------
// 选中某个色卡条目：复制色号 + 计算连通块
// ----------------------------------------------------------------------------
static void copyToClipboard(HWND hwnd, const std::wstring& text) {
    if (!OpenClipboard(hwnd)) return;
    EmptyClipboard();
    const size_t bytes = (text.size() + 1) * sizeof(wchar_t);
    HGLOBAL h = GlobalAlloc(GMEM_MOVEABLE, bytes);
    if (h) {
        void* p = GlobalLock(h);
        if (p) {
            memcpy(p, text.c_str(), bytes);
            GlobalUnlock(h);
            if (!SetClipboardData(CF_UNICODETEXT, h)) GlobalFree(h);
        } else {
            GlobalFree(h);
        }
    }
    CloseClipboard();
}

static void ensureVisible(int idx) {
    const int viewH = (int)(g_rcList.bottom - g_rcList.top);
    if (viewH <= 0) return;
    const int maxScroll = std::max(0, (int)g_pal.size() * ITEM_H - viewH);
    const int top = idx * ITEM_H - g_scroll;
    if (top < 0) g_scroll = idx * ITEM_H;
    else if (top + ITEM_H > viewH) g_scroll = idx * ITEM_H + ITEM_H - viewH;
    g_scroll = std::max(0, std::min(maxScroll, g_scroll));
}

static bool selectColor(int idx, bool copy) {
    if (g_pal.empty()) return false;
    if (idx < 0) idx = 0;
    if (idx >= (int)g_pal.size()) idx = (int)g_pal.size() - 1;
    g_sel = idx;
    ensureVisible(idx);

    const uint32_t rgb = g_pal[idx].rgb;
    computeContours(rgb);

    const std::wstring hx = hexOf(rgb);
    if (copy && g_hwnd) copyToClipboard(g_hwnd, hx);

    swprintf(g_status, 256, L"%s · 像素 %d 个 · 轮廓块 %d 个%s · %s",
             hx.c_str(), g_pal[idx].cnt, (int)g_comps.size(),
             g_truncated ? L"(显示已达上限)" : L"",
             copy ? L"色号已复制" : L"已按形状框出");
    refreshScrollBar();
    if (g_hwnd) InvalidateRect(g_hwnd, NULL, FALSE);
    return true;
}

static void selectNext(int delta) {
    if (g_pal.empty()) return;
    const int n = (int)g_pal.size();
    int idx = (g_sel < 0) ? 0 : g_sel + delta;
    idx = ((idx % n) + n) % n;          // 空格到末尾自动回到开头
    selectColor(idx, true);
}

// ----------------------------------------------------------------------------
// 像素拾取：点击图中任意像素，按所在四分象限从最近边缘计数其位置
//   象限划分：x < g_w/2 为左，否则为右；y < g_h/2 为上，否则为下
//   计数均为 1 基：左 => x+1，右 => g_w-x，上 => y+1，下 => g_h-y
// ----------------------------------------------------------------------------
static void recomputePickText() {
    g_pickText[0] = 0;
    if (g_pickX < 0 || g_pickY < 0 || g_pickX >= g_w || g_pickY >= g_h || g_w <= 0 || g_h <= 0)
        return;
    const int x = g_pickX, y = g_pickY;
    const bool left  = (x * 2 < g_w);
    const bool top   = (y * 2 < g_h);
    const int  hx    = left ? (x + 1) : (g_w - x);
    const int  hy    = top  ? (y + 1) : (g_h - y);
    const uint32_t c = g_px[(size_t)y * g_w + x];
    const std::wstring hxv = hexOf(c);
    swprintf(g_pickText, 160, L"[%ls%ls区] 横: %ls第 %d 个 · 纵: %ls第 %d 个 · %ls · 像素(%d,%d)",
             left ? L"左" : L"右", top ? L"上" : L"下",
             left ? L"左起" : L"右起", hx,
             top ? L"上起" : L"下起", hy,
             hxv.c_str(), x, y);
}

static void setPick(int px, int py) {
    if (g_w <= 0 || g_h <= 0) return;
    if (px < 0) px = 0;
    if (py < 0) py = 0;
    if (px >= g_w) px = g_w - 1;
    if (py >= g_h) py = g_h - 1;
    if (px == g_pickX && py == g_pickY) return;
    g_pickX = px;
    g_pickY = py;
    recomputePickText();
    if (g_hwnd) InvalidateRect(g_hwnd, NULL, FALSE);
}

static void clearPick() {
    if (g_pickX < 0 && g_pickY < 0) return;
    g_pickX = g_pickY = -1;
    g_pickText[0] = 0;
    if (g_hwnd) InvalidateRect(g_hwnd, NULL, FALSE);
}

// 客户区坐标 -> 图像像素坐标；不在图内返回 false
static bool clientToPixel(int cx, int cy, int& px, int& py) {
    if (!g_viewReady || g_w <= 0 || g_h <= 0) return false;
    const double s = g_viewS;
    if (!(s > 0)) return false;
    const double fx = (cx - g_viewOx) / s;
    const double fy = (cy - g_viewOy) / s;
    if (!(fx >= 0.0) || !(fy >= 0.0)) return false;
    const long long ix = (long long)std::floor(fx);
    const long long iy = (long long)std::floor(fy);
    if (ix >= g_w || iy >= g_h) return false;
    px = (int)ix;
    py = (int)iy;
    return true;
}

// ----------------------------------------------------------------------------
// 绘制
// ----------------------------------------------------------------------------
static void drawPick(Graphics& g, double scale, double ox, double oy) {
    if (g_pickX < 0 || g_pickY < 0) return;
    const double bx = ox + g_pickX * scale;          // 像素左上角（屏幕坐标）
    const double by = oy + g_pickY * scale;
    const double iw = scale, ih = scale;

    // 十字准线：贯穿整幅图，白描底 + 青色主线
    const double half = std::max(1.0, scale * 0.5);
    const Pen guideThinL(Color(200, 255, 255, 255), (REAL)std::max(1.0, half));
    const Pen guideCyan (Color(255, 40, 220, 255), (REAL)std::max(1.0, half));
    g.DrawLine(&guideThinL, (REAL)ox, (REAL)(by + half), (REAL)(ox + g_w * scale), (REAL)(by + half));
    g.DrawLine(&guideThinL, (REAL)(bx + half), (REAL)oy, (REAL)(bx + half), (REAL)(oy + g_h * scale));
    g.DrawLine(&guideCyan,  (REAL)ox, (REAL)(by + half), (REAL)(ox + g_w * scale), (REAL)(by + half));
    g.DrawLine(&guideCyan,  (REAL)(bx + half), (REAL)oy, (REAL)(bx + half), (REAL)(oy + g_h * scale));

    // 选中像素边框：内白外黑，保证任何底色都可见
    const double inset = std::max(0.0, half * 0.5);
    const Pen pickOuter(Color(255, 0, 0, 0), (REAL)std::max(1.0, half * 0.6));
    const Pen pickInner(Color(255, 255, 255, 255), (REAL)std::max(1.0, half * 0.6));
    g.DrawRectangle(&pickOuter, (REAL)(bx - inset), (REAL)(by - inset),
                    (REAL)(iw + inset * 2), (REAL)(ih + inset * 2));
    g.DrawRectangle(&pickInner, (REAL)(bx - inset), (REAL)(by - inset),
                    (REAL)(iw + inset * 2), (REAL)(ih + inset * 2));
}

static void drawOverlay(Graphics& g, double scale, double ox, double oy) {
    if (g_sel < 0) return;
    double lw = 2.0 * scale;
    if (lw < 1.0) lw = 1.0;
    if (lw > 3.0) lw = 3.0;

    const SmoothingMode prev = g.GetSmoothingMode();
    g.SetSmoothingMode(SmoothingModeAntiAlias);

    const Pen thin(Color(255, 255, 255, 255), (REAL)(lw * 0.7));   // 白描底保证可见
    const Pen hot (Color(255, 255, 45, 65), (REAL)lw);            // 红：实际形状轮廓

    std::vector<PointF> pts;
    for (size_t i = 0; i < g_comps.size(); ++i) {
        const Contour& c = g_comps[i];
        const size_t rings = c.ringStart.size();
        for (size_t r = 0; r < rings; ++r) {
            const int s = c.ringStart[r];
            const int e = (r + 1 < rings) ? c.ringStart[r + 1] : (int)c.xs.size();
            const int n = e - s;
            if (n < 2) continue;
            pts.clear();
            pts.reserve(n);
            // GDI+ 偶数宽笔触以像素边界为基准，且 AA 栅格化对线的右/下端执行
            // 向上取整：整数坐标 p 处的线覆盖 [p-1..p]，而右/下侧边界点却覆盖到
            // [p..p+1]，不对称 => 轮廓整体向右下偏半像素（右边/下边多一列墨）。
            // 网格点统一 -0.5 平移后取整归一为 floor，2px 线在每条边界上固定覆盖
            // "外侧一列 + 内侧一列"，四边对称、与像素分界线对齐。
            for (int k = s; k < e; ++k)
                pts.push_back(PointF((REAL)(ox + (c.xs[k] - 0.5) * scale),
                                     (REAL)(oy + (c.ys[k] - 0.5) * scale)));
            // 闭合多边形（首尾自动相连）
            g.DrawPolygon(&thin, pts.data(), (INT)pts.size());
            g.DrawPolygon(&hot,  pts.data(), (INT)pts.size());
        }
    }
    g.SetSmoothingMode(prev);
}

static void paint(HWND hwnd) {
    PAINTSTRUCT ps;
    HDC hdc = BeginPaint(hwnd, &ps);

    RECT rc; GetClientRect(hwnd, &rc);
    const int cw = rc.right, ch = rc.bottom;
    if (cw <= 0 || ch <= 0) { EndPaint(hwnd, &ps); return; }

    HDC mem = CreateCompatibleDC(hdc);
    HBITMAP hbmp = CreateCompatibleBitmap(hdc, cw, ch);
    HBITMAP old = (HBITMAP)SelectObject(mem, hbmp);

    {
        Graphics g(mem);
        g.SetSmoothingMode(SmoothingModeNone);
        g.SetInterpolationMode(InterpolationModeNearestNeighbor);
        g.Clear(Color(255, 34, 36, 40));

        const SolidBrush panelBg(Color(255, 24, 26, 30));
        const SolidBrush btnBg    (Color(255, 45, 92, 200));
        const SolidBrush white    (Color(255, 255, 255, 255));
        const SolidBrush dim      (Color(255, 190, 196, 206));
        const SolidBrush itemTxt  (Color(255, 226, 230, 238));
        const SolidBrush selRowBg (Color(255, 48, 52, 62));
        const Pen        itemPen  (Color(255, 70, 72, 80), 1);
        const Pen        selPen   (Color(255, 255, 210, 60), 2);
        const Pen        divPen   (Color(255, 60, 63, 70), 1);
        StringFormat sfL, sfC;
        sfL.SetLineAlignment(StringAlignmentCenter);
        sfL.SetTrimming(StringTrimmingEllipsisCharacter);
        sfC.SetAlignment(StringAlignmentCenter);
        sfC.SetLineAlignment(StringAlignmentCenter);

        // ---- 左侧色卡面板 ----
        g.FillRectangle(&panelBg, 0, 0, PALETTE_W, ch);
        g.DrawLine(&divPen, PALETTE_W - 1, 0, PALETTE_W - 1, ch);

        g_rcBtn = { 10, 10, PALETTE_W - 10, 40 };
        g.FillRectangle(&btnBg, (REAL)g_rcBtn.left, (REAL)g_rcBtn.top,
                        (REAL)(g_rcBtn.right - g_rcBtn.left), (REAL)(g_rcBtn.bottom - g_rcBtn.top));
        g.DrawString(L"打开图片 (O)", -1, g_font,
                     RectF((REAL)g_rcBtn.left, (REAL)g_rcBtn.top,
                           (REAL)(g_rcBtn.right - g_rcBtn.left), (REAL)(g_rcBtn.bottom - g_rcBtn.top)),
                     &sfC, &white);

        {
            std::wstring info = g_pal.empty()
                ? std::wstring(L"色卡：空")
                : (L"色卡 " + std::to_wstring(g_pal.size()) + L" 色 · 按均值升序");
            g.DrawString(info.c_str(), -1, g_fontSm,
                         RectF(10, (REAL)HEADER_H - 20, (REAL)(PALETTE_W - 14), 18), &sfL, &dim);
        }
        g.DrawString(L"空格 = 下一个颜色", -1, g_fontSm,
                     RectF(10, (REAL)HEADER_H - 2, (REAL)(PALETTE_W - 14), 18), &sfL, &dim);

        g_rcList = { 0, HEADER_H + 16, PALETTE_W, ch };
        const int viewH = (int)(g_rcList.bottom - g_rcList.top);
        {
            Region prev;
            g.GetClip(&prev);
            g.SetClip(RectF(0, (REAL)g_rcList.top, (REAL)PALETTE_W, (REAL)viewH));
            const int first = g_scroll / ITEM_H;
            const int last  = std::min((int)g_pal.size() - 1, first + viewH / ITEM_H + 2);
            for (int i = first; i <= last; ++i) {
                const REAL y = (REAL)(g_rcList.top + i * ITEM_H - g_scroll);
                const ColorInfo& ci = g_pal[i];
                if (i == g_sel)
                    g.FillRectangle(&selRowBg, (REAL)0, y, (REAL)PALETTE_W, (REAL)ITEM_H);
                const SolidBrush sw(Color(255, (BYTE)((ci.rgb >> 16) & 255),
                                              (BYTE)((ci.rgb >> 8) & 255),
                                              (BYTE)(ci.rgb & 255)));
                const REAL sy = y + (REAL)((ITEM_H - SWATCH) / 2);
                g.FillRectangle(&sw, (REAL)8, sy, (REAL)SWATCH, (REAL)SWATCH);
                g.DrawRectangle(&itemPen, (REAL)8, sy, (REAL)SWATCH, (REAL)SWATCH);
                const std::wstring hx = hexOf(ci.rgb);
                g.DrawString(hx.c_str(), -1, g_font,
                             RectF(34, y, (REAL)(PALETTE_W - 40), (REAL)ITEM_H), &sfL, &itemTxt);
                if (i == g_sel)
                    g.DrawRectangle(&selPen, (REAL)1, y + 1.0f, (REAL)(PALETTE_W - 3), (REAL)(ITEM_H - 2));
            }
            g.ResetClip();
            g.SetClip(&prev);
        }

        // ---- 右侧图像区 ----
        const int vx = PALETTE_W + 10, vy = 8;
        const int vw = cw - vx - 14, vh = ch - vy - STATUS_H - 10;
        g_rcImage = { vx, vy, vx + (vw > 0 ? vw : 0), vy + (vh > 0 ? vh : 0) };

        if (!g_bmp) {
            g_viewReady = false;
            g.DrawString(L"点击「打开图片」，或把图片拖进这个窗口",
                         -1, g_font,
                         RectF((REAL)vx, (REAL)vy, (REAL)(vw > 0 ? vw : 1), (REAL)(vh > 0 ? vh : 1)),
                         &sfC, &dim);
        } else {
            double s = std::min((double)vw / g_w, (double)vh / g_h);
            if (!(s > 0)) s = 1.0;
            const double dw = g_w * s, dh = g_h * s;
            const double ox = vx + (vw - dw) / 2.0, oy = vy + (vh - dh) / 2.0;
            g_viewS = s; g_viewOx = ox; g_viewOy = oy; g_viewReady = true;

            const Pen framePen(Color(255, 95, 98, 106), (REAL)1);
            g.DrawRectangle(&framePen,
                            (REAL)(ox - 1), (REAL)(oy - 1), (REAL)(dw + 2), (REAL)(dh + 2));
            g.DrawImage(g_bmp, RectF((REAL)ox, (REAL)oy, (REAL)dw, (REAL)dh),
                        0, 0, g_w, g_h, UnitPixel);

            Region prev;
            g.GetClip(&prev);
            g.SetClip(RectF((REAL)ox, (REAL)oy, (REAL)dw, (REAL)dh));
            drawOverlay(g, s, ox, oy);
            drawPick(g, s, ox, oy);
            g.ResetClip();
            g.SetClip(&prev);
        }

        // ---- 状态栏 ----
        {
            std::wstring st = g_status[0] ? std::wstring(g_status)
                          : (g_path.empty() ? std::wstring(L"未载入图片") : std::wstring(L"就绪"));
            g.DrawString(st.c_str(), -1, g_font,
                         RectF((REAL)vx, (REAL)(ch - STATUS_H), (REAL)(cw - vx - 8), (REAL)STATUS_H),
                         &sfL, &itemTxt);
            if (g_pickText[0]) {
                const std::wstring pt(g_pickText);
                SizeF box = { 0, 0 };
                g.MeasureString(pt.c_str(), -1, g_fontSm, SizeF(9999.0f, 9999.0f), &sfL, &box);
                int pw = (int)box.Width + 16;
                if (pw > (cw - vx - 8) / 2) pw = (cw - vx - 8) / 2;
                const REAL px0 = (REAL)(cw - 8 - pw);
                const SolidBrush pickBg(Color(255, 22, 48, 58));
                const Pen        pickBd(Color(255, 40, 220, 255), 1);
                g.FillRectangle(&pickBg, px0, (REAL)(ch - STATUS_H + 3), (REAL)pw, (REAL)(STATUS_H - 6));
                g.DrawRectangle(&pickBd, px0, (REAL)(ch - STATUS_H + 3), (REAL)pw, (REAL)(STATUS_H - 6));
                g.DrawString(pt.c_str(), -1, g_fontSm,
                             RectF(px0 + 8, (REAL)(ch - STATUS_H), (REAL)(pw - 12), (REAL)STATUS_H),
                             &sfL, &white);
            }
        }
    }

    BitBlt(hdc, 0, 0, cw, ch, mem, 0, 0, SRCCOPY);
    SelectObject(mem, old);
    DeleteObject(hbmp);
    DeleteDC(mem);
    EndPaint(hwnd, &ps);
}

// ----------------------------------------------------------------------------
// 文件对话框 / 拖放
// ----------------------------------------------------------------------------
static void doOpen(HWND hwnd) {
    wchar_t file[MAX_PATH] = L"";
    OPENFILENAMEW ofn;
    ZeroMemory(&ofn, sizeof(ofn));
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner   = hwnd;
    ofn.lpstrFilter = L"图片文件\0*.png;*.jpg;*.jpeg;*.bmp;*.gif;*.tif;*.tiff;*.webp\0所有文件\0*.*\0";
    ofn.lpstrFile   = file;
    ofn.nMaxFile    = MAX_PATH;
    ofn.lpstrTitle  = L"选择图片";
    ofn.Flags       = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_HIDEREADONLY;
    if (GetOpenFileNameW(&ofn)) {
        if (!openImage(file))
            MessageBoxW(hwnd, L"无法读取该图片文件（格式不受支持或文件损坏）。", L"ColorPick",
                        MB_OK | MB_ICONWARNING);
    }
}

// ----------------------------------------------------------------------------
// 窗口过程
// ----------------------------------------------------------------------------
static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_ERASEBKGND:
        return 1;                                   // WM_PAINT 已全量绘制（双缓冲）

    case WM_SIZE:
        refreshScrollBar();
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;

    case WM_PAINT:
        paint(hwnd);
        return 0;

    case WM_LBUTTONDOWN: {
        const int x = GET_X_LPARAM(lp), y = GET_Y_LPARAM(lp);
        if (hit(g_rcBtn, x, y)) { doOpen(hwnd); return 0; }
        if (hit(g_rcList, x, y) && !g_pal.empty()) {
            const int idx = (y - g_rcList.top + g_scroll) / ITEM_H;
            if (idx >= 0 && idx < (int)g_pal.size()) selectColor(idx, true);
            SetFocus(hwnd);
            return 0;
        }
        int px = -1, py = -1;
        if (clientToPixel(x, y, px, py)) {           // 点在图上：拾取该像素
            setPick(px, py);
            g_pickDrag = true;
            SetCapture(hwnd);
        } else {
            clearPick();                             // 点在图外空白：清除标记
        }
        SetFocus(hwnd);
        return 0;
    }

    case WM_MOUSEMOVE: {
        if (g_pickDrag && (GET_KEYSTATE_WPARAM(wp) & MK_LBUTTON)) {
            int px = -1, py = -1;
            if (clientToPixel(GET_X_LPARAM(lp), GET_Y_LPARAM(lp), px, py)) setPick(px, py);
        }
        return 0;
    }

    case WM_LBUTTONUP:
        if (g_pickDrag) { g_pickDrag = false; if (GetCapture() == hwnd) ReleaseCapture(); }
        return 0;

    case WM_CAPTURECHANGED:
        g_pickDrag = false;
        return 0;

    case WM_SETCURSOR:
        if ((HWND)wp == hwnd && LOWORD(lp) == HTCLIENT) {
            POINT pt; GetCursorPos(&pt); ScreenToClient(hwnd, &pt);
            if (g_bmp && hit(g_rcImage, pt.x, pt.y)) {
                SetCursor(LoadCursor(NULL, IDC_CROSS));   // 图上用十字光标便于对齐像素
                return TRUE;
            }
        }
        return DefWindowProc(hwnd, msg, wp, lp);

    case WM_MOUSEWHEEL: {
        POINT pt = { GET_X_LPARAM(lp), GET_Y_LPARAM(lp) };
        ScreenToClient(hwnd, &pt);
        if (hit(g_rcList, pt.x, pt.y) && !g_pal.empty()) {
            const int viewH = g_rcList.bottom - g_rcList.top;
            const int maxScroll = std::max(0, (int)g_pal.size() * ITEM_H - viewH);
            g_scroll -= (GET_WHEEL_DELTA_WPARAM(wp) / WHEEL_DELTA) * ITEM_H * 3;
            g_scroll = std::max(0, std::min(maxScroll, g_scroll));
            refreshScrollBar();
            InvalidateRect(hwnd, NULL, FALSE);
            return 0;
        }
        return DefWindowProc(hwnd, msg, wp, lp);
    }

    case WM_VSCROLL: {
        if (g_pal.empty()) return 0;
        const int viewH = g_rcList.bottom - g_rcList.top;
        const int maxScroll = std::max(0, (int)g_pal.size() * ITEM_H - viewH);
        int pos = g_scroll;
        switch (LOWORD(wp)) {
        case SB_LINEUP:     pos -= ITEM_H; break;
        case SB_LINEDOWN:   pos += ITEM_H; break;
        case SB_PAGEUP:     pos -= viewH;  break;
        case SB_PAGEDOWN:   pos += viewH;  break;
        case SB_THUMBTRACK:
        case SB_THUMBPOSITION: {
            SCROLLINFO si = { sizeof(si), SIF_TRACKPOS };
            GetScrollInfo(hwnd, SB_VERT, &si);
            const int denom = std::max(1, (int)g_pal.size() - 1);
            pos = MulDiv(si.nTrackPos, maxScroll, denom);
            break;
        }
        case SB_TOP:        pos = 0;         break;
        case SB_BOTTOM:     pos = maxScroll; break;
        }
        g_scroll = std::max(0, std::min(maxScroll, pos));
        InvalidateRect(hwnd, NULL, FALSE);
        return 0;
    }

    case WM_KEYDOWN: {
        const bool ctrl  = (GetKeyState(VK_CONTROL) & 0x8000) != 0;
        const bool shift = (GetKeyState(VK_SHIFT)   & 0x8000) != 0;
        switch (wp) {
        case VK_SPACE:  selectNext(shift ? -1 : +1); return 0;
        case VK_ADD:    case VK_OEM_PLUS:      selectNext(+1); return 0;
        case VK_SUBTRACT: case VK_OEM_MINUS:   selectNext(-1); return 0;
        case VK_UP:
            if (shift) selectNext(-1);
            else if (!g_pal.empty()) selectColor(g_sel < 0 ? 0 : g_sel - 1, true);
            return 0;
        case VK_DOWN:
            if (shift) selectNext(+1);
            else if (!g_pal.empty()) selectColor(g_sel < 0 ? 0 : g_sel + 1, true);
            return 0;
        case VK_HOME: if (!g_pal.empty()) selectColor(0, true); return 0;
        case VK_END:  if (!g_pal.empty()) selectColor((int)g_pal.size() - 1, true); return 0;
        case VK_ESCAPE: clearSelection(); clearPick(); InvalidateRect(hwnd, NULL, FALSE); return 0;
        case 'O':
            doOpen(hwnd);
            return 0;
        default:
            if (ctrl && wp == 'O') { doOpen(hwnd); return 0; }
            return 0;
        }
    }

    case WM_CHAR:
        if (wp == ' ' || wp == 15) return 0;        // 已在 WM_KEYDOWN 处理，避免重复触发
        return 0;

    case WM_DROPFILES: {
        HDROP hdrop = (HDROP)wp;
        wchar_t file[MAX_PATH] = L"";
        if (DragQueryFileW(hdrop, 0, file, MAX_PATH) && file[0]) {
            if (!openImage(file))
                MessageBoxW(hwnd, L"无法读取该图片文件（格式不受支持或文件损坏）。",
                            L"ColorPick", MB_OK | MB_ICONWARNING);
        }
        DragFinish(hdrop);
        return 0;
    }

    case WM_GETMINMAXINFO: {
        MINMAXINFO* mmi = (MINMAXINFO*)lp;
        mmi->ptMinTrackSize.x = 620;
        mmi->ptMinTrackSize.y = 360;
        return 0;
    }

    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProc(hwnd, msg, wp, lp);
}

// ----------------------------------------------------------------------------
// 自检模式（无界面）：验证色卡覆盖、排序、十六进制、连通块面积、PNG 输出
// ----------------------------------------------------------------------------
static Status savePng(Bitmap* bmp, const wchar_t* path) {
    CLSID pngClsid;
    bool found = false;
    UINT num = 0, size = 0;
    GetImageEncodersSize(&num, &size);
    if (size) {
        std::vector<BYTE> buf(size);
        ImageCodecInfo* encs = (ImageCodecInfo*)buf.data();
        if (GetImageEncoders(num, size, encs) == Ok) {
            for (UINT i = 0; i < num; ++i) {
                if (encs[i].MimeType && wcscmp(encs[i].MimeType, L"image/png") == 0) {
                    pngClsid = encs[i].Clsid; found = true; break;
                }
            }
        }
    }
    if (!found) return GenericError;
    return bmp->Save(path, &pngClsid, NULL);
}

static int selftest(int argc, wchar_t** argv) {
    const std::wstring in     = argc > 2 ? argv[2] : L"";
    const std::wstring outPng = argc > 3 ? argv[3] : L"";
    const std::wstring logPath= argc > 4 ? argv[4] : L"selftest.log";

    g_logf = _wfopen(logPath.c_str(), L"w, ccs=UTF-8");
    if (in.empty()) { say("[selftest] FAIL: missing input image\n"); return 2; }

    int W = 0, H = 0;
    std::vector<uint32_t> px;
    Bitmap* b = loadBitmapFrom(in.c_str(), W, H, px);
    if (!b) { say("[selftest] FAIL: cannot load image\n"); if (g_logf) fclose(g_logf); return 3; }

    g_bmp = b; g_w = W; g_h = H; g_px = std::move(px);
    g_inMask.assign((size_t)W * H, 0);
    buildPalette();
    say("[selftest] image %dx%d  unique colors=%zu\n", W, H, g_pal.size());
    if (g_pal.empty()) { say("[selftest] FAIL: empty palette\n"); return 4; }

    bool pass = true;

    // (1) 排序不变式：三通道和必须严格单调不减（即均值升序）
    bool sortedOk = true;
    for (size_t i = 1; i < g_pal.size(); ++i)
        if (chanSum(g_pal[i].rgb) < chanSum(g_pal[i - 1].rgb)) { sortedOk = false; break; }
    say("[selftest] palette sorted by mean asc      : %s\n", sortedOk ? "PASS" : "FAIL");
    pass &= sortedOk;

    // (2) 色卡覆盖所有出现过的颜色，计数与真实直方图一致
    std::unordered_map<uint32_t, int> hist;
    for (size_t i = 0; i < g_px.size(); ++i) ++hist[g_px[i]];
    bool coverOk = (hist.size() == g_pal.size());
    for (size_t i = 0; i < g_pal.size() && coverOk; ++i) {
        std::unordered_map<uint32_t, int>::iterator it = hist.find(g_pal[i].rgb);
        if (it == hist.end() || it->second != g_pal[i].cnt) coverOk = false;
    }
    say("[selftest] palette == full histogram       : %s\n", coverOk ? "PASS" : "FAIL");
    pass &= coverOk;

    // (3) 十六进制格式化 / 反解析
    {
        const std::wstring h0 = hexOf(0x1A2B3Cu);
        const bool okFmt = (h0 == L"#1A2B3C");
        uint32_t back = 0;
        const bool okParse = parseHex(L"#1a2b3c", back) && back == 0x1A2B3Cu;
        say("[selftest] hexOf -> %ls                  : %s\n", h0.c_str(), okFmt ? "PASS" : "FAIL");
        say("[selftest] parseHex(#1a2b3c)=0x%06X      : %s\n", back, okParse ? "PASS" : "FAIL");
        pass &= okFmt && okParse;
    }

    // (4) 轮廓：像素数守恒 + 每个环闭合 + 外环鞋带面积绝对值 == 块像素数
    //     （沿像素边走线的阶梯多边形，其鞋带面积精确等于覆盖的像素数，
    //      这能强校验轮廓确实描出了实际形状而不是矩形框）
    const int probe = (int)std::min<size_t>(g_pal.size(), 6);
    bool compOk = true;
    for (int i = 0; i < probe; ++i) {
        const uint32_t rgb = g_pal[i].rgb;
        computeContours(rgb);
        long long sumArea = 0;
        for (size_t k = 0; k < g_comps.size(); ++k) {
            const Contour& c = g_comps[k];
            sumArea += c.area;
            if (c.area <= 0 || c.ringStart.empty()) { compOk = false; continue; }
            if (c.x0 < 0 || c.y0 < 0 || c.x1 >= W || c.y1 >= H || c.x1 < c.x0 || c.y1 < c.y0) compOk = false;

            // 对所有环求带符号鞋带面积：外环为正、内孔环为负，总和/2 必须等于块像素数。
            // 这能同时验证「沿像素边描出的实际形状」和「孔洞也被正确描出」。
            long long signed2 = 0;
            const size_t rings = c.ringStart.size();
            for (size_t r = 0; r < rings; ++r) {
                const int s = c.ringStart[r];
                const int e = (r + 1 < rings) ? c.ringStart[r + 1] : (int)c.xs.size();
                const int n = e - s;
                if (n < 4) { compOk = false; continue; }   // 至少 1 像素 => 4 个网格点
                for (int t = 0; t < n; ++t) {
                    const int a = s + t, b = s + (t + 1) % n;
                    signed2 += (long long)c.xs[a] * c.ys[b] - (long long)c.xs[b] * c.ys[a];
                    const int dx = abs(c.xs[b] - c.xs[a]), dy = abs(c.ys[b] - c.ys[a]);
                    if (dx + dy != 1) compOk = false;      // 每步只能沿网格走 1 格
                }
                for (int t = 0; t < n; ++t) {              // 环点必须落在网格范围内
                    if (c.xs[s + t] < 0 || c.xs[s + t] > W || c.ys[s + t] < 0 || c.ys[s + t] > H) compOk = false;
                }
            }
            if (signed2 / 2 != c.area) {
                compOk = false;
                say("[selftest]   comp %zu: signedArea=%lld expect=%d rings=%zu\n",
                    k, signed2 / 2, c.area, c.ringStart.size());
            }
        }
        const long long expect = hist[rgb];
        if (sumArea != expect) compOk = false;
        say("[selftest] #%d %ls mean=%.2f px=%lld comps=%zu sumArea=%lld\n",
            i, hexOf(rgb).c_str(), chanSum(rgb) / 3.0, expect, g_comps.size(), sumArea);
    }
    say("[selftest] contour area == pixel count   : %s\n", compOk ? "PASS" : "FAIL");
    pass &= compOk;

    // (5) 非矩形形状校验：L 形/凹形的轮廓点数应明显多于矩形的 4 个
    {
        // 找一个块：其轮廓外环点数 > 4 且其外接矩形面积 > 块面积（即确实不是矩形）
        bool foundNonRect = false, nonRectOk = true;
        for (size_t k = 0; k < g_comps.size(); ++k) {
            const Contour& c = g_comps[k];
            const int bw = c.x1 - c.x0 + 1, bh = c.y1 - c.y0 + 1;
            if ((long long)bw * bh > c.area) {          // 非矩形（有缺口）
                foundNonRect = true;
                const int s = c.ringStart[0];
                const int e = (c.ringStart.size() > 1) ? c.ringStart[1] : (int)c.xs.size();
                if (e - s <= 4) nonRectOk = false;      // 应描出阶梯轮廓，点数多于 4
                say("[selftest] non-rect comp bbox %dx%d area %d ringPts %d\n",
                    bw, bh, c.area, e - s);
            }
        }
        say("[selftest] non-rectangular shape traced   : %s (%s)\n",
            foundNonRect ? (nonRectOk ? "PASS" : "FAIL") : "SKIP",
            foundNonRect ? "non-rect found" : "all comps are rectangles");
        if (foundNonRect) pass &= nonRectOk;
    }

    // (6) 像素拾取位置：四象限从最近边缘计数（1 基），需与独立实现完全一致
    {
        bool pickOk = true;
        const struct { int x, y; const wchar_t* want; } probes[] = {
            {       0,       0, L"[左上区] 横: 左起第 1 个 · 纵: 上起第 1 个" },
            {       1,       3, L"[左上区] 横: 左起第 2 个 · 纵: 上起第 4 个" },
            { W / 2 - 1,      0, NULL },
            { W / 2,       0, NULL },                      // x*2 == W 归右
            {     W - 1,   H - 1, L"[右下区] 横: 右起第 1 个 · 纵: 下起第 1 个" },
            {     W - 2, H - 4, L"[右下区] 横: 右起第 2 个 · 纵: 下起第 4 个" },
            {       0,   H - 1, L"[左下区] 横: 左起第 1 个 · 纵: 下起第 1 个" },
            {     W - 1,   H / 2 - 1, NULL },
        };
        for (size_t t = 0; t < sizeof(probes) / sizeof(probes[0]); ++t) {
            const int x = probes[t].x, y = probes[t].y;
            g_pickX = x; g_pickY = y;
            recomputePickText();
            // 独立重算：左 => x+1 / 右 => W-x，上 => y+1 / 下 => H-y
            const bool left = (x * 2 < W), top = (y * 2 < H);
            const int hx = left ? x + 1 : W - x, hy = top ? y + 1 : H - y;
            wchar_t want[64];
            swprintf(want, 64, L"[%ls%ls区] 横: %ls第 %d 个 · 纵: %ls第 %d 个",
                     left ? L"左" : L"右", top ? L"上" : L"下",
                     left ? L"左起" : L"右起", hx, top ? L"上起" : L"下起", hy);
            const bool prefixOk = (wcsncmp(g_pickText, want, wcslen(want)) == 0);
            if (!prefixOk) {
                pickOk = false;
                say("[selftest]   pick(%d,%d): got=%ls want=%ls\n", x, y, g_pickText, want);
            }
        }
        // 越界像素必须被拒绝显示
        g_pickX = W; g_pickY = 0; recomputePickText();
        if (g_pickText[0]) { pickOk = false; say("[selftest]   pick out-of-range not cleared\n"); }
        // 四角与中心都应在文本里给出 1 基的边缘距离
        say("[selftest] pixel pick quadrant counting   : %s\n", pickOk ? "PASS" : "FAIL");
        pass &= pickOk;
        g_pickX = g_pickY = -1; g_pickText[0] = 0;
    }

    // (7) 渲染叠加图（验证 GDI+ 绘制 + PNG 编码链路可用）
    if (!outPng.empty()) {
        int pick = 0;
        if (argc > 5) {
            const std::wstring a = argv[5];
            uint32_t rgb = 0;
            bool matched = false;
            if (parseHex(a.c_str(), rgb)) {
                for (size_t i = 0; i < g_pal.size(); ++i)
                    if (g_pal[i].rgb == rgb) { pick = (int)i; matched = true; break; }
                if (!matched) say("[selftest] WARN: %ls not found in palette\n", a.c_str());
            } else {
                pick = _wtoi(a.c_str());
            }
        }
        selectColor(pick, false);
        Bitmap* out = new Bitmap(g_w, g_h, PixelFormat32bppRGB);
        {
            Graphics og(out);
            og.SetInterpolationMode(InterpolationModeNearestNeighbor);
            og.DrawImage(g_bmp, Rect(0, 0, g_w, g_h), 0, 0, g_w, g_h, UnitPixel);
            og.SetSmoothingMode(SmoothingModeNone);
            drawOverlay(og, 1.0, 0.0, 0.0);
        }
        const Status st = savePng(out, outPng.c_str());
        say("[selftest] overlay png (%ls) sel=#%d comps=%zu : %s\n",
            outPng.c_str(), pick, g_comps.size(), st == Ok ? "PASS" : "FAIL");
        pass &= (st == Ok);
        delete out;
    }

    say("[selftest] RESULT: %s\n", pass ? "ALL PASS" : "FAILED");
    if (g_logf) { fclose(g_logf); g_logf = NULL; }
    return pass ? 0 : 1;
}

// ----------------------------------------------------------------------------
// 入口
// ----------------------------------------------------------------------------
static Font* makeFont(float size, UINT style) {
    const wchar_t* names[] = { L"Microsoft YaHei UI", L"Microsoft YaHei", L"Segoe UI" };
    for (int i = 0; i < 3; ++i) {
        FontFamily* ff = new FontFamily(names[i]);
        if (ff->GetLastStatus() == Ok) {
            Font* f = new Font(ff, size, style, UnitPixel);
            delete g_ff;
            g_ff = ff;
            if (f->GetLastStatus() == Ok) return f;
            delete f;
            break;
        }
        delete ff;
    }
    g_ff = new FontFamily(L"SansSerif");
    return new Font(g_ff, size, style, UnitPixel);
}

int WINAPI WinMain(HINSTANCE hInst, HINSTANCE, LPSTR, int) {
    g_hInst = hInst;

    int argc = 0;
    LPWSTR* argv = CommandLineToArgvW(GetCommandLineW(), &argc);

    GdiplusStartupInput gsi;
    if (GdiplusStartup(&g_gdipToken, &gsi, NULL) != Ok) return 1;

    if (argc > 1 && _wcsicmp(argv[1], L"--selftest") == 0) {
        const int rc = selftest(argc, argv);
        GdiplusShutdown(g_gdipToken);
        return rc;
    }

    g_font   = makeFont(12.0f, FontStyleRegular);
    g_fontSm = new Font(g_ff, 11.0f, FontStyleRegular, UnitPixel);

    WNDCLASSEXW wc;
    ZeroMemory(&wc, sizeof(wc));
    wc.cbSize        = sizeof(wc);
    wc.style         = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc   = WndProc;
    wc.hInstance     = hInst;
    wc.hCursor       = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = NULL;
    wc.lpszClassName = L"ColorPickWindowClass";
    wc.hIcon         = LoadIcon(NULL, IDI_APPLICATION);
    RegisterClassExW(&wc);

    HWND hwnd = CreateWindowExW(
        0, wc.lpszClassName, L"ColorPick",
        WS_OVERLAPPEDWINDOW | WS_VSCROLL,
        CW_USEDEFAULT, CW_USEDEFAULT, 1240, 820,
        NULL, NULL, hInst, NULL);
    if (!hwnd) return 1;
    g_hwnd = hwnd;

    DragAcceptFiles(hwnd, TRUE);
    ShowWindow(hwnd, SW_SHOW);
    UpdateWindow(hwnd);
    SetFocus(hwnd);

    if (argc > 1 && argv[1][0] != L'-') openImage(argv[1]);

    MSG m;
    for (;;) {
        const BOOL r = GetMessage(&m, NULL, 0, 0);
        if (r == 0 || r == (BOOL)-1) break;
        if (m.message == WM_KEYDOWN && (m.wParam == VK_SPACE || m.wParam == VK_UP ||
            m.wParam == VK_DOWN || m.wParam == VK_LEFT || m.wParam == VK_RIGHT)) {
            // 拦截方向键/空格的系统导航，交给窗口过程处理
        }
        TranslateMessage(&m);
        DispatchMessage(&m);
    }

    delete g_bmp;    g_bmp = NULL;
    delete g_font;   delete g_fontSm;
    delete g_ff;
    GdiplusShutdown(g_gdipToken);
    return 0;
}
