#define _DEFAULT_SOURCE

#include <unicorn/unicorn.h>

#include <SDL2/SDL.h>
#include <SDL2/SDL_ttf.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>

#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <dirent.h>
#include <fnmatch.h>
#include <time.h>

#define MEM_SIZE        0x110000
#define VIDEO_ADDR      0xB8000
#define VID_COLS        80
#define VID_ROWS        25

#define COM_LOAD_OFFSET 0x0100
#define ENV_SEG         0x2000
#define MZ_LOAD_SEG     0x1000

#define SCREEN_W        (VID_COLS * 8)
#define SCREEN_H        (VID_ROWS * 16)

/* DOS error codes */
#define DOS_ERR_SUCCESS         0
#define DOS_ERR_INVALID_FUNC    1
#define DOS_ERR_FILE_NOT_FOUND  2
#define DOS_ERR_PATH_NOT_FOUND  3
#define DOS_ERR_TOO_MANY_FILES  4
#define DOS_ERR_ACCESS_DENIED   5
#define DOS_ERR_INVALID_HANDLE  6
#define DOS_ERR_NO_MEMORY       8
#define DOS_ERR_INVALID_DATA    13
#define DOS_ERR_INVALID_DRIVE   15
#define DOS_ERR_SAME_DEVICE     16
#define DOS_ERR_NO_MORE_FILES   18

static uc_engine *uc;
static bool emu_running = true;
static bool in_emulation = false;

static int dos_handles[255];
static int max_dos_handles = 32;

static uint16_t current_psp_seg = 0;
static uint32_t current_dta = 0x80;
static uint16_t alloc_seg = 0x3000;

static DIR *find_dir = NULL;
static char find_dirpath[512];
static char find_pattern[512]; /* FIXED: was 256, caused truncation warning */

static int cur_row = 0;
static int cur_col = 0;
static uint8_t cur_attr = 0x07;

static bool ctrl_break_enabled = false;

static SDL_Window *sdl_window;
static SDL_Renderer *sdl_renderer;
static TTF_Font *sdl_font;
static SDL_Texture *glyph_cache[256];

static int mouse_x = 0;
static int mouse_y = 0;
static int mouse_buttons = 0;
static int mouse_min_x = 0;
static int mouse_max_x = SCREEN_W - 1;
static int mouse_min_y = 0;
static int mouse_max_y = SCREEN_H - 1;
static int mouse_mickey_x = 0;
static int mouse_mickey_y = 0;

#define KEY_QUEUE_SIZE 256
static uint16_t key_queue[KEY_QUEUE_SIZE];
static int key_head = 0;
static int key_tail = 0;

typedef struct {
    uint16_t magic;
    uint16_t cblp;
    uint16_t cp;
    uint16_t crlc;
    uint16_t cparhdr;
    uint16_t minalloc;
    uint16_t maxalloc;
    uint16_t ss;
    uint16_t sp;
    uint16_t csum;
    uint16_t ip;
    uint16_t cs;
    uint16_t lfarlc;
    uint16_t ovno;
} __attribute__((packed)) MZHeader;

static const SDL_Color cga_colors[16] = {
    {  0,   0,   0, 255},
    {  0,   0, 170, 255},
    {  0, 170,   0, 255},
    {  0, 170, 170, 255},
    {170,   0,   0, 255},
    {170,   0, 170, 255},
    {170,  85,   0, 255},
    {170, 170, 170, 255},
    { 85,  85,  85, 255},
    { 85,  85, 255, 255},
    { 85, 255,  85, 255},
    { 85, 255, 255, 255},
    {255,  85,  85, 255},
    {255,  85, 255, 255},
    {255, 255,  85, 255},
    {255, 255, 255, 255},
};

static const unsigned char vga_font[96][16] = {
    {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0x00,0x18,0x3C,0x3C,0x3C,0x18,0x18,0x00,0x18,0x18,0x00,0,0,0,0,0},
    {0x00,0x66,0x66,0x24,0x00,0,0,0,0,0,0,0,0,0,0,0},
    {0x00,0x6C,0x6C,0xFE,0x6C,0x6C,0x6C,0xFE,0x6C,0x6C,0x00,0,0,0,0,0},
    {0x18,0x18,0x7C,0xC6,0xC2,0xC0,0x7C,0x06,0x86,0xC6,0x7C,0x18,0x18,0,0,0},
    {0x00,0x00,0xC2,0xC6,0x0C,0x18,0x30,0x60,0xC6,0x86,0x00,0,0,0,0,0},
    {0x00,0x38,0x6C,0x6C,0x38,0x76,0xDC,0xCC,0xCC,0x76,0x00,0,0,0,0,0},
    {0x00,0x30,0x30,0x60,0x00,0,0,0,0,0,0,0,0,0,0,0},
    {0x00,0x0C,0x18,0x30,0x30,0x30,0x30,0x30,0x18,0x0C,0x00,0,0,0,0,0},
    {0x00,0x30,0x18,0x0C,0x0C,0x0C,0x0C,0x0C,0x18,0x30,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x66,0x3C,0xFF,0x3C,0x66,0x00,0,0,0,0,0,0,0},
    {0x00,0x00,0x00,0x18,0x18,0x7E,0x18,0x18,0x00,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0x18,0x18,0x30,0,0,0,0,0,0},
    {0,0,0,0,0,0xFE,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0x18,0x18,0,0,0,0,0,0},
    {0x00,0x00,0x02,0x06,0x0C,0x18,0x30,0x60,0xC0,0x80,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0xCE,0xDE,0xF6,0xE6,0xC6,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x18,0x38,0x78,0x18,0x18,0x18,0x18,0x18,0x7E,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0x06,0x0C,0x18,0x30,0x60,0xC6,0xFE,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0x06,0x06,0x3C,0x06,0x06,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x0C,0x1C,0x3C,0x6C,0xCC,0xFE,0x0C,0x0C,0x1E,0x00,0,0,0,0,0},
    {0x00,0xFE,0xC0,0xC0,0xC0,0xFC,0x06,0x06,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x38,0x60,0xC0,0xC0,0xFC,0xC6,0xC6,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0xFE,0xC6,0x06,0x06,0x0C,0x18,0x30,0x30,0x30,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0xC6,0xC6,0x7C,0xC6,0xC6,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0xC6,0xC6,0x7E,0x06,0x06,0x0C,0x78,0x00,0,0,0,0,0},
    {0,0,0,0x18,0x18,0,0,0x18,0x18,0,0,0,0,0,0,0},
    {0,0,0,0x18,0x18,0,0,0x18,0x18,0x30,0,0,0,0,0,0},
    {0x00,0x00,0x06,0x0C,0x18,0x30,0x60,0x30,0x18,0x0C,0x06,0x00,0,0,0,0},
    {0,0,0,0,0x7E,0,0,0x7E,0,0,0,0,0,0,0,0},
    {0x00,0x00,0x60,0x30,0x18,0x0C,0x06,0x0C,0x18,0x30,0x60,0x00,0,0,0,0},
    {0x00,0x7C,0xC6,0xC6,0x0C,0x18,0x18,0x00,0x18,0x18,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0xC6,0xDE,0xDE,0xDE,0xDC,0xC0,0x7C,0x00,0,0,0,0,0},
    {0x00,0x10,0x38,0x6C,0xC6,0xC6,0xFE,0xC6,0xC6,0xC6,0x00,0,0,0,0,0},
    {0x00,0xFC,0x66,0x66,0x66,0x7C,0x66,0x66,0x66,0xFC,0x00,0,0,0,0,0},
    {0x00,0x3C,0x66,0xC2,0xC0,0xC0,0xC0,0xC2,0x66,0x3C,0x00,0,0,0,0,0},
    {0x00,0xF8,0x6C,0x66,0x66,0x66,0x66,0x66,0x6C,0xF8,0x00,0,0,0,0,0},
    {0x00,0xFE,0x66,0x62,0x68,0x78,0x68,0x62,0x66,0xFE,0x00,0,0,0,0,0},
    {0x00,0xFE,0x66,0x62,0x68,0x78,0x68,0x60,0x60,0xF0,0x00,0,0,0,0,0},
    {0x00,0x3C,0x66,0xC2,0xC0,0xDE,0xC6,0xC6,0x66,0x3A,0x00,0,0,0,0,0},
    {0x00,0xC6,0xC6,0xC6,0xC6,0xFE,0xC6,0xC6,0xC6,0xC6,0x00,0,0,0,0,0},
    {0x00,0x3C,0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x3C,0x00,0,0,0,0,0},
    {0x00,0x1E,0x0C,0x0C,0x0C,0x0C,0xCC,0xCC,0xCC,0x78,0x00,0,0,0,0,0},
    {0x00,0xE6,0x66,0x6C,0x6C,0x78,0x6C,0x6C,0x66,0xE6,0x00,0,0,0,0,0},
    {0x00,0xF0,0x60,0x60,0x60,0x60,0x62,0x66,0x66,0xFE,0x00,0,0,0,0,0},
    {0x00,0xC6,0xEE,0xFE,0xFE,0xD6,0xC6,0xC6,0xC6,0xC6,0x00,0,0,0,0,0},
    {0x00,0xC6,0xE6,0xF6,0xFE,0xDE,0xCE,0xC6,0xC6,0xC6,0x00,0,0,0,0,0},
    {0x00,0x38,0x6C,0xC6,0xC6,0xC6,0xC6,0xC6,0x6C,0x38,0x00,0,0,0,0,0},
    {0x00,0xFC,0x66,0x66,0x66,0x7C,0x60,0x60,0x60,0xF0,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0xC6,0xC6,0xC6,0xD6,0xDE,0x7C,0x0C,0x0E,0x00,0,0,0,0},
    {0x00,0xFC,0x66,0x66,0x66,0x7C,0x6C,0x66,0x66,0xE6,0x00,0,0,0,0,0},
    {0x00,0x7C,0xC6,0xC6,0x60,0x38,0x0C,0xC6,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0xFF,0xDB,0x99,0x18,0x18,0x18,0x18,0x18,0x3C,0x00,0,0,0,0,0},
    {0x00,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0xC6,0xC6,0xC6,0xC6,0xC6,0xC6,0x6C,0x38,0x10,0x00,0,0,0,0,0},
    {0x00,0xC6,0xC6,0xC6,0xD6,0xD6,0xFE,0x6C,0x6C,0x6C,0x00,0,0,0,0,0},
    {0x00,0xC6,0xC6,0x6C,0x38,0x38,0x38,0x6C,0xC6,0xC6,0x00,0,0,0,0,0},
    {0x00,0xCC,0xCC,0xCC,0xCC,0x78,0x30,0x30,0x30,0x78,0x00,0,0,0,0,0},
    {0x00,0xFE,0xC6,0x86,0x0C,0x18,0x30,0x60,0xC2,0xFE,0x00,0,0,0,0,0},
    {0x00,0x3C,0x30,0x30,0x30,0x30,0x30,0x30,0x30,0x3C,0x00,0,0,0,0,0},
    {0x00,0x00,0x80,0xC0,0x60,0x30,0x18,0x0C,0x06,0x02,0x00,0,0,0,0,0},
    {0x00,0x3C,0x0C,0x0C,0x0C,0x0C,0x0C,0x0C,0x0C,0x3C,0x00,0,0,0,0,0},
    {0x10,0x38,0x6C,0xC6,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,0,0,0,0,0xFF,0,0,0,0,0,0},
    {0x30,0x18,0x0C,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0x78,0x0C,0x7C,0xCC,0xCC,0x76,0x00,0,0,0,0,0},
    {0x00,0xE0,0x60,0x60,0x7C,0x66,0x66,0x66,0x66,0xDC,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0x7C,0xC6,0xC0,0xC0,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x1C,0x0C,0x0C,0x7C,0xCC,0xCC,0xCC,0xCC,0x76,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0x7C,0xC6,0xFE,0xC0,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x1C,0x36,0x30,0x30,0xFC,0x30,0x30,0x30,0x78,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0x76,0xCC,0xCC,0xCC,0x7C,0x0C,0xCC,0x78,0x00,0,0,0,0},
    {0x00,0xE0,0x60,0x60,0x6C,0x76,0x66,0x66,0x66,0xE6,0x00,0,0,0,0,0},
    {0x00,0x18,0x18,0x00,0x78,0x18,0x18,0x18,0x18,0x7E,0x00,0,0,0,0,0},
    {0x00,0x06,0x06,0x00,0x3E,0x06,0x06,0x06,0x06,0x66,0x66,0x3C,0x00,0,0,0,0},
    {0x00,0xE0,0x60,0x60,0x66,0x6C,0x78,0x6C,0x66,0xE6,0x00,0,0,0,0,0},
    {0x00,0x78,0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x7E,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xEC,0xFE,0xD6,0xD6,0xD6,0xC6,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xDC,0x66,0x66,0x66,0x66,0x66,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0x7C,0xC6,0xC6,0xC6,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xDC,0x66,0x66,0x66,0x7C,0x60,0x60,0xF0,0x00,0,0,0,0},
    {0x00,0x00,0x00,0x00,0x76,0xCC,0xCC,0xCC,0x7C,0x0C,0x0C,0x1E,0x00,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xDC,0x76,0x62,0x60,0x60,0xF0,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0x7C,0xC6,0x70,0x1C,0xC6,0x7C,0x00,0,0,0,0,0},
    {0x00,0x10,0x30,0x30,0xFC,0x30,0x30,0x30,0x36,0x1C,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xCC,0xCC,0xCC,0xCC,0xCC,0x76,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xC6,0xC6,0xC6,0x6C,0x38,0x10,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xC6,0xC6,0xD6,0xFE,0x6C,0x6C,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xC6,0x6C,0x38,0x38,0x6C,0xC6,0x00,0,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xC6,0xC6,0xC6,0xC6,0x7E,0x06,0x0C,0xF8,0x00,0,0,0,0},
    {0x00,0x00,0x00,0x00,0xFE,0x4C,0x18,0x32,0x66,0xFE,0x00,0,0,0,0,0},
    {0x00,0x0E,0x18,0x18,0x18,0x70,0x18,0x18,0x18,0x0E,0x00,0,0,0,0,0},
    {0x18,0x18,0x18,0x18,0x00,0x18,0x18,0x18,0x18,0x18,0x00,0,0,0,0,0},
    {0x00,0x70,0x18,0x18,0x18,0x0E,0x18,0x18,0x18,0x70,0x00,0,0,0,0,0},
    {0x76,0xDC,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0x00,0x10,0x38,0x6C,0xC6,0xC6,0xFE,0x00,0,0,0,0,0,0,0,0},
};

static SDL_Texture *make_bitmap_glyph(uint8_t ch)
{
    const unsigned char *glyph;
    if (ch >= 0x20 && ch <= 0x7F)
        glyph = vga_font[ch - 0x20];
    else
        glyph = vga_font['?' - 0x20];

    uint32_t pixels[8 * 16];
    for (int y = 0; y < 16; y++) {
        unsigned char row = glyph[y];
        for (int x = 0; x < 8; x++)
            pixels[y * 8 + x] = (row & (0x80 >> x)) ? 0xFFFFFFFFu : 0x00000000u;
    }

    SDL_Texture *tex = SDL_CreateTexture(sdl_renderer,
                                         SDL_PIXELFORMAT_ARGB8888,
                                         SDL_TEXTUREACCESS_STATIC, 8, 16);
    if (!tex)
        return NULL;
    SDL_SetTextureBlendMode(tex, SDL_BLENDMODE_BLEND);
    SDL_UpdateTexture(tex, NULL, pixels, 8 * (int)sizeof(uint32_t));
    return tex;
}

static uint32_t seg_off_to_linear(uint16_t seg, uint16_t off)
{
    return ((uint32_t)seg << 4) + off;
}

static uint16_t reg16_read(uc_engine *u, int reg)
{
    uint16_t v = 0;
    uc_reg_read(u, reg, &v);
    return v;
}

static void reg16_write(uc_engine *u, int reg, uint16_t v)
{
    uc_reg_write(u, reg, &v);
}

static uint32_t reg32_read(uc_engine *u, int reg)
{
    uint32_t v = 0;
    uc_reg_read(u, reg, &v);
    return v;
}

static void reg32_write(uc_engine *u, int reg, uint32_t v)
{
    uc_reg_write(u, reg, &v);
}

static void advance_ip(uc_engine *u, uint32_t delta)
{
    uint32_t ip = reg32_read(u, UC_X86_REG_EIP);
    uint8_t opcode = 0;
    uc_mem_read(u, ip, &opcode, 1);

    if (delta == 2 && opcode == 0xCD) {
        ip = (ip + 2) & 0xFFFF;
        reg32_write(u, UC_X86_REG_EIP, ip);
    } else if (delta == 1 && opcode == 0xCC) {
        ip = (ip + 1) & 0xFFFF;
        reg32_write(u, UC_X86_REG_EIP, ip);
    }
}

static void flags_modify(uc_engine *u, uint32_t set_bits, uint32_t clear_bits)
{
    uint32_t f = reg32_read(u, UC_X86_REG_EFLAGS);
    f |= set_bits;
    f &= ~clear_bits;
    reg32_write(u, UC_X86_REG_EFLAGS, f);
}

static void set_cf(uc_engine *u, bool carry)
{
    if (carry)
        flags_modify(u, 1, 0);
    else
        flags_modify(u, 0, 1);
}

static void set_zf(uc_engine *u, bool zero)
{
    if (zero)
        flags_modify(u, 0x40, 0);
    else
        flags_modify(u, 0, 0x40);
}

static void stop_emulation(uc_engine *u)
{
    emu_running = false;
    if (in_emulation)
        uc_emu_stop(u);
}

static void dos_error(uc_engine *u, uint16_t code)
{
    reg16_write(u, UC_X86_REG_AX, code);
    set_cf(u, true);
}

static void dos_success(uc_engine *u)
{
    set_cf(u, false);
}

static bool key_empty(void)
{
    return key_head == key_tail;
}

static void key_clear(void)
{
    key_head = key_tail = 0;
}

static void key_push_code(uint16_t code)
{
    int next = (key_tail + 1) % KEY_QUEUE_SIZE;
    if (next == key_head)
        return;

    key_queue[key_tail] = code;
    key_tail = next;
}

static uint16_t key_peek(void)
{
    if (key_empty())
        return 0;
    return key_queue[key_head];
}

static uint16_t key_pop(void)
{
    if (key_empty())
        return 0;

    uint16_t v = key_queue[key_head];
    key_head = (key_head + 1) % KEY_QUEUE_SIZE;
    return v;
}

static void video_set_cell(uc_engine *u, int row, int col, uint8_t ch, uint8_t attr)
{
    if (row < 0 || row >= VID_ROWS || col < 0 || col >= VID_COLS)
        return;

    uint32_t addr = VIDEO_ADDR + (row * VID_COLS + col) * 2;
    uint8_t cell[2] = {ch, attr};
    uc_mem_write(u, addr, cell, 2);
}

static uint16_t video_get_cell(uc_engine *u, int row, int col)
{
    if (row < 0 || row >= VID_ROWS || col < 0 || col >= VID_COLS)
        return 0x0700;

    uint32_t addr = VIDEO_ADDR + (row * VID_COLS + col) * 2;
    uint8_t cell[2] = {0, 7};
    uc_mem_read(u, addr, cell, 2);
    return cell[0] | (cell[1] << 8);
}

static void video_clear_region(uc_engine *u, int top, int left, int bottom, int right, uint8_t attr)
{
    if (top < 0) top = 0;
    if (left < 0) left = 0;
    if (bottom >= VID_ROWS) bottom = VID_ROWS - 1;
    if (right >= VID_COLS) right = VID_COLS - 1;

    for (int r = top; r <= bottom; r++) {
        for (int c = left; c <= right; c++) {
            video_set_cell(u, r, c, ' ', attr);
        }
    }
}

static void video_scroll_up_region(uc_engine *u, int top, int left, int bottom, int right, uint8_t attr, int lines)
{
    if (top < 0) top = 0;
    if (left < 0) left = 0;
    if (bottom >= VID_ROWS) bottom = VID_ROWS - 1;
    if (right >= VID_COLS) right = VID_COLS - 1;

    if (lines <= 0)
        return;

    if (lines >= (bottom - top + 1)) {
        video_clear_region(u, top, left, bottom, right, attr);
        return;
    }

    for (int r = top; r <= bottom; r++) {
        int src = r + lines;

        for (int c = left; c <= right; c++) {
            if (src <= bottom) {
                uint16_t cell = video_get_cell(u, src, c);
                video_set_cell(u, r, c, cell & 0xFF, cell >> 8);
            } else {
                video_set_cell(u, r, c, ' ', attr);
            }
        }
    }
}

static void video_scroll_down_region(uc_engine *u, int top, int left, int bottom, int right, uint8_t attr, int lines)
{
    if (top < 0) top = 0;
    if (left < 0) left = 0;
    if (bottom >= VID_ROWS) bottom = VID_ROWS - 1;
    if (right >= VID_COLS) right = VID_COLS - 1;

    if (lines <= 0)
        return;

    if (lines >= (bottom - top + 1)) {
        video_clear_region(u, top, left, bottom, right, attr);
        return;
    }

    for (int r = bottom; r >= top; r--) {
        int src = r - lines;

        for (int c = left; c <= right; c++) {
            if (src >= top) {
                uint16_t cell = video_get_cell(u, src, c);
                video_set_cell(u, r, c, cell & 0xFF, cell >> 8);
            } else {
                video_set_cell(u, r, c, ' ', attr);
            }
        }
    }
}

static void video_init(uc_engine *u)
{
    video_clear_region(u, 0, 0, VID_ROWS - 1, VID_COLS - 1, 0x07);
    cur_row = 0;
    cur_col = 0;
    cur_attr = 0x07;
}

static void video_putc(uc_engine *u, uint8_t ch, uint8_t attr)
{


    if (ch == 0x0D) putchar('\r');
    else if (ch == 0x0A) { putchar('\n'); fflush(stdout); }
    else if (ch >= 0x20 && ch < 0x7F) { putchar(ch); fflush(stdout); }

    if (ch == 0x08) {
        if (cur_col > 0)
            cur_col--;
        video_set_cell(u, cur_row, cur_col, ' ', attr);
        return;
    }

    if (ch == 0x0D) {
        cur_col = 0;
        return;
    }

    if (ch == 0x0A) {
        cur_row++;
        if (cur_row >= VID_ROWS) {
            cur_row = VID_ROWS - 1;
            video_scroll_up_region(u, 0, 0, VID_ROWS - 1, VID_COLS - 1, attr, 1);
        }
        return;
    }

    if (ch == 0x07)
        return;

    video_set_cell(u, cur_row, cur_col, ch, attr);

    cur_col++;
    if (cur_col >= VID_COLS) {
        cur_col = 0;
        cur_row++;
        if (cur_row >= VID_ROWS) {
            cur_row = VID_ROWS - 1;
            video_scroll_up_region(u, 0, 0, VID_ROWS - 1, VID_COLS - 1, attr, 1);
        }
    }
}

static SDL_Texture *get_glyph_texture(uint8_t ch)
{
    if (glyph_cache[ch])
        return glyph_cache[ch];

    SDL_Texture *tex = make_bitmap_glyph(ch);
    if (tex)
        glyph_cache[ch] = tex;
    return tex;
}

static void render_video(uc_engine *u)
{
    if (!sdl_renderer)
        return;

    SDL_SetRenderDrawColor(sdl_renderer, 0, 0, 0, 255);
    SDL_RenderClear(sdl_renderer);

    uint8_t vmem[VID_COLS * VID_ROWS * 2];

    if (uc_mem_read(u, VIDEO_ADDR, vmem, sizeof(vmem)) != UC_ERR_OK)
        return;

    for (int i = 0; i < VID_COLS * VID_ROWS; i++) {
        uint8_t ch = vmem[i * 2];
        uint8_t attr = vmem[i * 2 + 1];

        int row = i / VID_COLS;
        int col = i % VID_COLS;

        SDL_Rect rect = {
            .x = col * 8,
            .y = row * 16,
            .w = 8,
            .h = 16
        };

        int fg = attr & 0x0F;
        int bg = (attr >> 4) & 0x0F;

        SDL_Color bgc = cga_colors[bg];
        SDL_Color fgc = cga_colors[fg];

        SDL_SetRenderDrawColor(sdl_renderer, bgc.r, bgc.g, bgc.b, 255);
        SDL_RenderFillRect(sdl_renderer, &rect);

        if (ch != 0 && ch != ' ') {
            SDL_Texture *tex = get_glyph_texture(ch);

            if (tex) {
                SDL_SetTextureColorMod(tex, fgc.r, fgc.g, fgc.b);
                SDL_RenderCopy(sdl_renderer, tex, NULL, &rect);
            } else {
                SDL_Rect inner = {
                    .x = rect.x + 2,
                    .y = rect.y + 4,
                    .w = 4,
                    .h = 8
                };

                SDL_SetRenderDrawColor(sdl_renderer, fgc.r, fgc.g, fgc.b, 255);
                SDL_RenderFillRect(sdl_renderer, &inner);
            }
        }
    }

    SDL_RenderPresent(sdl_renderer);
}

static bool sdl_init(void)
{
    if (SDL_Init(SDL_INIT_VIDEO) != 0) {
        fprintf(stderr, "SDL_Init failed: %s\n", SDL_GetError());
        return false;
    }

    if (TTF_Init() != 0) {
        fprintf(stderr, "TTF_Init failed: %s\n", TTF_GetError());
        return false;
    }

    sdl_window = SDL_CreateWindow(
        "DOSExecute C",
        SDL_WINDOWPOS_CENTERED,
        SDL_WINDOWPOS_CENTERED,
        SCREEN_W,
        SCREEN_H,
        0
    );

    if (!sdl_window) {
        fprintf(stderr, "SDL_CreateWindow failed: %s\n", SDL_GetError());
        return false;
    }

    sdl_renderer = SDL_CreateRenderer(sdl_window, -1, SDL_RENDERER_ACCELERATED);
    if (!sdl_renderer) {
        fprintf(stderr, "SDL_CreateRenderer failed: %s\n", SDL_GetError());
        return false;
    }

    const char *font_paths[] = {
        "/usr/share/fonts/dejavu/DejaVuSansMono.ttf",
        "/usr/share/fonts/dejavu/DejaVuSansMono-Bold.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
        "/usr/share/fonts/TTF/DejaVuSansMono.ttf",
        NULL
    };

    for (int i = 0; font_paths[i]; i++) {
        sdl_font = TTF_OpenFont(font_paths[i], 16);
        if (sdl_font)
            break;
    }

    memset(glyph_cache, 0, sizeof(glyph_cache));

    SDL_ShowCursor(SDL_ENABLE);

    return true;
}

static void sdl_shutdown(void)
{
    for (int i = 0; i < 256; i++) {
        if (glyph_cache[i])
            SDL_DestroyTexture(glyph_cache[i]);
    }

    if (sdl_font)
        TTF_CloseFont(sdl_font);

    if (sdl_renderer)
        SDL_DestroyRenderer(sdl_renderer);

    if (sdl_window)
        SDL_DestroyWindow(sdl_window);

    TTF_Quit();
    SDL_Quit();
}

static void push_ascii(uint8_t ascii)
{
    key_push_code(ascii);
}

static void push_bios(uint8_t scan, uint8_t ascii)
{
    key_push_code(((uint16_t)scan << 8) | ascii);
}

static void handle_keydown(SDL_KeyboardEvent *e)
{
    bool ctrl = (e->keysym.mod & KMOD_CTRL) != 0;
    SDL_Keycode sym = e->keysym.sym;

    if (ctrl && sym >= SDLK_a && sym <= SDLK_z) {
        push_ascii(sym - SDLK_a + 1);
        return;
    }

    if (sym >= SDLK_F1 && sym <= SDLK_F10) {
        uint8_t scan = 0x3B + (sym - SDLK_F1);
        push_bios(scan, 0);
        return;
    }

    switch (sym) {
        case SDLK_F11:
            push_bios(0x57, 0);
            return;
        case SDLK_F12:
            push_bios(0x58, 0);
            return;

        case SDLK_RETURN:
        case SDLK_KP_ENTER:
            push_bios(0x1C, 13);
            return;

        case SDLK_ESCAPE:
            push_bios(0x01, 27);
            return;

        case SDLK_BACKSPACE:
            push_bios(0x0E, 8);
            return;

        case SDLK_TAB:
            push_bios(0x0F, 9);
            return;

        case SDLK_SPACE:
            push_bios(0x39, ' ');
            return;

        case SDLK_UP:
            push_bios(0x48, 0);
            return;
        case SDLK_DOWN:
            push_bios(0x50, 0);
            return;
        case SDLK_LEFT:
            push_bios(0x4B, 0);
            return;
        case SDLK_RIGHT:
            push_bios(0x4D, 0);
            return;

        case SDLK_HOME:
            push_bios(0x47, 0);
            return;
        case SDLK_END:
            push_bios(0x4F, 0);
            return;
        case SDLK_PAGEUP:
            push_bios(0x49, 0);
            return;
        case SDLK_PAGEDOWN:
            push_bios(0x51, 0);
            return;
        case SDLK_INSERT:
            push_bios(0x52, 0);
            return;
        case SDLK_DELETE:
            push_bios(0x53, 0);
            return;

        default:
            break;
    }
}

static void clamp_mouse(void)
{
    if (mouse_x < mouse_min_x) mouse_x = mouse_min_x;
    if (mouse_x > mouse_max_x) mouse_x = mouse_max_x;
    if (mouse_y < mouse_min_y) mouse_y = mouse_min_y;
    if (mouse_y > mouse_max_y) mouse_y = mouse_max_y;
}

static void process_sdl_events(uc_engine *u)
{
    SDL_Event ev;

    while (SDL_PollEvent(&ev)) {
        switch (ev.type) {

            case SDL_QUIT:
                stop_emulation(u);
                break;

            case SDL_KEYDOWN:
                handle_keydown(&ev.key);
                break;

            case SDL_TEXTINPUT: {
                unsigned char *p = (unsigned char *)ev.text.text;
                if (p[0] >= 32 && p[0] < 127 && p[1] == 0)
                    push_ascii(p[0]);
                break;
            }

            case SDL_MOUSEMOTION: {
                int dx = ev.motion.xrel;
                int dy = ev.motion.yrel;

                mouse_x += dx;
                mouse_y += dy;

                mouse_mickey_x += dx;
                mouse_mickey_y += dy;

                clamp_mouse();
                break;
            }

            case SDL_MOUSEBUTTONDOWN:
            case SDL_MOUSEBUTTONUP: {
                int mask = 0;

                if (ev.button.button == SDL_BUTTON_LEFT)
                    mask = 1;
                else if (ev.button.button == SDL_BUTTON_RIGHT)
                    mask = 2;
                else if (ev.button.button == SDL_BUTTON_MIDDLE)
                    mask = 4;

                if (ev.type == SDL_MOUSEBUTTONDOWN)
                    mouse_buttons |= mask;
                else
                    mouse_buttons &= ~mask;

                break;
            }

            default:
                break;
        }
    }
}

static uint16_t wait_bios_key(uc_engine *u)
{
    while (emu_running && key_empty()) {
        process_sdl_events(u);
        render_video(u);
        SDL_Delay(1);
    }

    if (!emu_running)
        return 0;

    return key_pop();
}

static uint8_t wait_ascii_key(uc_engine *u)
{
    while (emu_running) {
        uint16_t k = wait_bios_key(u);

        if (!emu_running)
            return 0;

        if ((k & 0xFF) != 0)
            return k & 0xFF;
    }

    return 0;
}

static void init_dos_handles(void)
{
    for (int i = 0; i < 255; i++)
        dos_handles[i] = -1;

    dos_handles[0] = 0;
    dos_handles[1] = 1;
    dos_handles[2] = 2;
}

static int alloc_dos_handle(int fd)
{
    for (int i = 3; i < max_dos_handles; i++) {
        if (dos_handles[i] == -1) {
            dos_handles[i] = fd;
            return i;
        }
    }

    close(fd);
    return -1;
}

static bool valid_handle(int h)
{
    return h >= 0 && h < max_dos_handles && dos_handles[h] >= 0;
}

static int guest_read_cstring(uc_engine *u, uint32_t addr, char *out, size_t outsz)
{
    size_t i = 0;

    while (i + 1 < outsz) {
        uint8_t c = 0;

        if (uc_mem_read(u, addr + i, &c, 1) != UC_ERR_OK)
            return -1;

        out[i++] = (char)c;

        if (c == 0)
            break;
    }

    out[i] = 0;
    return 0;
}

static void guest_write_cstring(uc_engine *u, uint32_t addr, const char *s, size_t maxlen)
{
    size_t len = strlen(s);
    if (len > maxlen)
        len = maxlen;

    uc_mem_write(u, addr, s, len);

    uint8_t zero = 0;
    uc_mem_write(u, addr + len, &zero, 1);
}

static char host_cwd[512];

static int read_dos_path(uc_engine *u, uint16_t seg, uint16_t off, char *host, size_t hostsz)
{
    char guest[512];
    if (guest_read_cstring(u, seg_off_to_linear(seg, off), guest, sizeof(guest)) != 0)
        return -1;

    const char *p = guest;
    int had_drive = 0;

    /* Strip drive letter (C:, D:, ...) */
    if (p[0] != 0 && p[1] == ':') { p += 2; had_drive = 1; }

    /* Convert backslashes to slashes into a relative path */
    char rel[512];
    size_t j = 0;
    while (*p && j + 1 < sizeof(rel)) {
        char c = *p++;
        if (c == '\\') c = '/';
        rel[j++] = c;
    }
    rel[j] = 0;

    /* Strip leading '/' so the path is relative to the C: root */
    const char *r = rel;
    while (*r == '/') r++;

    #ifdef _WIN32
    /* Windows: C:\ is a real drive. Rebuild an absolute path if a drive was given. */
    if (had_drive)
        snprintf(host, hostsz, "C:\\%s", r);
    else
        snprintf(host, hostsz, "%s", r);
    #else
    /* Linux: the emulated C:\ == the directory the emulator was started in. */
    if (getcwd(host_cwd, sizeof(host_cwd)) == NULL)
        host_cwd[0] = 0;
    snprintf(host, hostsz, "%s/%s", host_cwd, r);
    #endif
    return 0;
}

static void unix_to_dos_datetime(time_t t, uint16_t *dos_date, uint16_t *dos_time)
{
    struct tm *tm = localtime(&t);
    int year = tm->tm_year + 1900;

    if (year < 1980) {
        *dos_date = 0x0021;
        *dos_time = 0;
        return;
    }

    *dos_date =
    ((year - 1980) << 9) |
    ((tm->tm_mon + 1) << 5) |
    tm->tm_mday;

    *dos_time =
    (tm->tm_hour << 11) |
    (tm->tm_min << 5) |
    (tm->tm_sec / 2);
}

static void split_path(const char *path, char *dir, size_t dirsz, char *pat, size_t patsz)
{
    const char *slash = strrchr(path, '/');
    #ifdef _WIN32
    const char *bslash = strrchr(path, '\\');
    if (bslash && (!slash || bslash > slash)) slash = bslash;
    #endif

    if (slash) {
        size_t len = (size_t)(slash - path);
        if (len == 0)
            snprintf(dir, dirsz, "/");
        else {
            if (len >= dirsz) len = dirsz - 1;
            memcpy(dir, path, len);
            dir[len] = 0;
        }
        snprintf(pat, patsz, "%s", slash + 1);
    } else {
        snprintf(dir, dirsz, ".");
        snprintf(pat, patsz, "%s", path);
    }

    if (pat[0] == 0)
        snprintf(pat, patsz, "*");
    if (strcmp(pat, "*.*") == 0)
        snprintf(pat, patsz, "*");
}

static void make_dos_name(char *out, const char *in)
{
    size_t j = 0;

    while (in[j] && j < 12) {
        out[j] = (char)toupper((unsigned char)in[j]);
        j++;
    }

    out[j] = 0;
}

static bool find_next_entry(char *name, uint8_t *attr, uint16_t *date, uint16_t *time, uint32_t *size)
{
    if (!find_dir)
        return false;

    struct dirent *de;

    while ((de = readdir(find_dir)) != NULL) {
        if (strcmp(de->d_name, ".") == 0 || strcmp(de->d_name, "..") == 0)
            continue;

        if (fnmatch(find_pattern, de->d_name, 0) != 0)
            continue;

        char full[1024];
        snprintf(full, sizeof(full), "%s/%s", find_dirpath, de->d_name);

        struct stat st;
        if (stat(full, &st) != 0)
            continue;

        *attr = 0;

        if (S_ISDIR(st.st_mode))
            *attr |= 0x10;

        if (!(st.st_mode & S_IWUSR))
            *attr |= 0x01;

        unix_to_dos_datetime(st.st_mtime, date, time);

        *size = (uint32_t)st.st_size;

        make_dos_name(name, de->d_name);
        return true;
    }

    return false;
}

static void write_find_result(uc_engine *u, uint32_t dta,
                              const char *name,
                              uint8_t attr,
                              uint16_t date,
                              uint16_t time,
                              uint32_t size)
{
    uc_mem_write(u, dta + 21, &attr, 1);
    uc_mem_write(u, dta + 22, &time, 2);
    uc_mem_write(u, dta + 24, &date, 2);
    uc_mem_write(u, dta + 26, &size, 4);

    char dosname[13];
    memset(dosname, 0, sizeof(dosname));
    snprintf(dosname, sizeof(dosname), "%s", name);

    uc_mem_write(u, dta + 30, dosname, 13);
}

static void handle_int33(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);
    uint16_t bx = reg16_read(u, UC_X86_REG_BX);
    uint16_t cx = reg16_read(u, UC_X86_REG_CX);
    uint16_t dx = reg16_read(u, UC_X86_REG_DX);

    switch (ax) {

        case 0x0000:
            ax = 0xFFFF;
            bx = 2;
            mouse_x = 0;
            mouse_y = 0;
            mouse_buttons = 0;
            mouse_min_x = 0;
            mouse_min_y = 0;
            mouse_max_x = SCREEN_W - 1;
            mouse_max_y = SCREEN_H - 1;
            SDL_ShowCursor(SDL_ENABLE);
            break;

        case 0x0001:
            SDL_ShowCursor(SDL_ENABLE);
            break;

        case 0x0002:
            SDL_ShowCursor(SDL_DISABLE);
            break;

        case 0x0003:
            bx = mouse_buttons;
            cx = mouse_x;
            dx = mouse_y;
            break;

        case 0x0004:
            mouse_x = cx;
            mouse_y = dx;
            clamp_mouse();
            break;

        case 0x0005:
            ax = mouse_buttons;
            bx = mouse_buttons;
            cx = mouse_x;
            dx = mouse_y;
            break;

        case 0x0006:
            ax = mouse_buttons;
            bx = mouse_buttons;
            cx = mouse_x;
            dx = mouse_y;
            break;

        case 0x0007:
            mouse_min_x = cx;
            mouse_max_x = dx;
            clamp_mouse();
            break;

        case 0x0008:
            mouse_min_y = cx;
            mouse_max_y = dx;
            clamp_mouse();
            break;

        case 0x000F:
            ax = 8;
            break;

        case 0x000B:
            cx = mouse_mickey_x;
            dx = mouse_mickey_y;
            mouse_mickey_x = 0;
            mouse_mickey_y = 0;
            break;

        case 0x000C:
            break;

        case 0x0010:
            break;

        case 0x0013:
            break;

        case 0x0015:
            bx = 0;
            break;

        case 0x0016:
            bx = 0;
            break;

        case 0x0017:
            break;

        case 0x0018:
            cx = 0;
            break;

        case 0x0019:
            cx = 0;
            break;

        case 0x001A:
            bx = 1;
            break;

        case 0x001B:
            ax = 1;
            break;

        case 0x001C:
            break;

        case 0x001D:
            break;

        default:
            break;
    }

    reg16_write(u, UC_X86_REG_AX, ax);
    reg16_write(u, UC_X86_REG_BX, bx);
    reg16_write(u, UC_X86_REG_CX, cx);
    reg16_write(u, UC_X86_REG_DX, dx);
}

static void handle_int10(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);
    uint16_t bx = reg16_read(u, UC_X86_REG_BX);
    uint16_t cx = reg16_read(u, UC_X86_REG_CX);
    uint16_t dx = reg16_read(u, UC_X86_REG_DX);

    uint8_t ah = ax >> 8;
    uint8_t al = ax & 0xFF;

    switch (ah) {

        case 0x00:
            video_init(u);
            break;

        case 0x01:
            break;

        case 0x02:
            cur_row = dx >> 8;
            cur_col = dx & 0xFF;

            if (cur_row < 0) cur_row = 0;
            if (cur_row >= VID_ROWS) cur_row = VID_ROWS - 1;
            if (cur_col < 0) cur_col = 0;
            if (cur_col >= VID_COLS) cur_col = VID_COLS - 1;
            break;

        case 0x03:
            cx = 0x0607;
            dx = (cur_row << 8) | cur_col;
            break;

        case 0x06: {
            uint8_t attr = bx >> 8;
            int top = cx >> 8;
            int left = cx & 0xFF;
            int bottom = dx >> 8;
            int right = dx & 0xFF;

            if (al == 0)
                video_clear_region(u, top, left, bottom, right, attr);
            else
                video_scroll_up_region(u, top, left, bottom, right, attr, al);

            break;
        }

        case 0x07: {
            uint8_t attr = bx >> 8;
            int top = cx >> 8;
            int left = cx & 0xFF;
            int bottom = dx >> 8;
            int right = dx & 0xFF;

            if (al == 0)
                video_clear_region(u, top, left, bottom, right, attr);
            else
                video_scroll_down_region(u, top, left, bottom, right, attr, al);

            break;
        }

        case 0x08: {
            uint16_t cell = video_get_cell(u, cur_row, cur_col);
            ax = ((cell >> 8) << 8) | (cell & 0xFF);
            break;
        }

        case 0x09: {
            uint8_t ch = al;
            uint8_t attr = bx & 0xFF;
            int count = cx;

            int r = cur_row;
            int c = cur_col;

            for (int i = 0; i < count; i++) {
                video_set_cell(u, r, c, ch, attr);

                c++;
                if (c >= VID_COLS) {
                    c = 0;
                    r++;
                    if (r >= VID_ROWS)
                        r = 0;
                }
            }

            break;
        }

        case 0x0A: {
            uint8_t ch = al;
            int count = cx;

            int r = cur_row;
            int c = cur_col;

            for (int i = 0; i < count; i++) {
                uint16_t cell = video_get_cell(u, r, c);
                video_set_cell(u, r, c, ch, cell >> 8);

                c++;
                if (c >= VID_COLS) {
                    c = 0;
                    r++;
                    if (r >= VID_ROWS)
                        r = 0;
                }
            }

            break;
        }

        case 0x0E:
            video_putc(u, al, cur_attr);
            break;

        case 0x0F:
            ax = (VID_COLS << 8) | 3;
            bx = 0;
            break;

        case 0x13: {
            uint16_t es = reg16_read(u, UC_X86_REG_ES);
            uint16_t bp = reg16_read(u, UC_X86_REG_BP);
            uint32_t addr = seg_off_to_linear(es, bp);

            int count = cx;
            bool update_cursor = (al & 1) != 0;
            bool attr_in_string = (al & 2) != 0;
            uint8_t attr = bx & 0xFF;

            int saved_row = cur_row;
            int saved_col = cur_col;

            cur_row = dx >> 8;
            cur_col = dx & 0xFF;

            for (int i = 0; i < count; i++) {
                uint8_t ch = 0;
                uint8_t use_attr = attr;

                uc_mem_read(u, addr++, &ch, 1);

                if (attr_in_string)
                    uc_mem_read(u, addr++, &use_attr, 1);

                video_putc(u, ch, use_attr);
            }

            if (!update_cursor) {
                cur_row = saved_row;
                cur_col = saved_col;
            }

            break;
        }

        case 0x1A:
            ax = (ax & 0xFF00) | 0x1A;
            bx = 0;
            break;

        case 0x1B:
            ax = (ax & 0xFF00) | 0x1B;
            break;

        case 0x4F:
            ax = (ax & 0xFF00) | 0x01;
            break;

        default:
            break;
    }

    reg16_write(u, UC_X86_REG_AX, ax);
    reg16_write(u, UC_X86_REG_BX, bx);
    reg16_write(u, UC_X86_REG_CX, cx);
    reg16_write(u, UC_X86_REG_DX, dx);
}

static void handle_int16(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);
    uint8_t ah = ax >> 8;

    switch (ah) {

        case 0x00:
        case 0x10: {
            uint16_t k = wait_bios_key(u);
            ax = k;
            reg16_write(u, UC_X86_REG_AX, ax);
            break;
        }

        case 0x01:
        case 0x11: {
            if (!key_empty()) {
                ax = key_peek();
                set_zf(u, false);
            } else {
                ax = 0;
                set_zf(u, true);
            }

            reg16_write(u, UC_X86_REG_AX, ax);
            break;
        }

        case 0x02:
        case 0x12:
            ax = 0;
            reg16_write(u, UC_X86_REG_AX, ax);
            break;

        default:
            break;
    }
}

static void handle_int13(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);
    uint16_t bx = reg16_read(u, UC_X86_REG_BX);
    uint16_t cx = reg16_read(u, UC_X86_REG_CX);
    uint16_t dx = reg16_read(u, UC_X86_REG_DX);

    uint8_t ah = ax >> 8;
    uint8_t dl = dx & 0xFF;

    switch (ah) {
        case 0x00: /* Reset disk system */
            ax = (ax & 0xFF00) | 0x00;
            set_cf(u, false);
            break;

        case 0x01: /* Get status of last operation */
            ax = (ax & 0xFF00) | 0x00;
            set_cf(u, false);
            break;

        case 0x02: /* Read sectors */
        case 0x03: /* Write sectors */
        case 0x04: /* Verify sectors */
            /* Raw sector I/O not natively emulated, return invalid command error */
            ax = 0x0100;
            set_cf(u, true);
            break;

        case 0x08: /* Get drive parameters */
            if (dl == 0x00) { /* Floppy A: */
                ax = (ax & 0xFF00) | 0x00;
                bx = (bx & 0xFF00) | 0x04; /* 1.44M floppy */
                cx = 0x4F12; /* 80 cyls, 18 sectors */
                dx = 0x0101; /* 2 heads, 1 drive */
                set_cf(u, false);
            } else if (dl == 0x80) { /* HDD 0 */
                ax = (ax & 0xFF00) | 0x00;
                bx = (bx & 0xFF00) | 0x00;
                cx = 0xFFFF; /* 1024 cyls, 63 sectors */
                dx = 0x0F01; /* 16 heads, 1 drive */
                set_cf(u, false);
            } else {
                ax = (ax & 0xFF00) | 0x80; /* Timeout */
                set_cf(u, true);
            }
            break;

        case 0x15: /* Get disk type */
            if (dl == 0x80) {
                ax = (ax & 0xFF00) | 0x03; /* Hard disk present */
                cx = 0x000F; /* CX:DX = 1032192 sectors (~504 MB) */
                dx = 0xC000;
                set_cf(u, false);
            } else if (dl == 0x00) {
                ax = (ax & 0xFF00) | 0x01; /* Floppy present, no change-line */
                set_cf(u, false);
            } else {
                ax = (ax & 0xFF00) | 0x00; /* Not present */
                set_cf(u, true);
            }
            break;

        case 0x41: /* Check INT 13h extensions */
            set_cf(u, true); /* Not supported */
            break;

        default:
            ax = (ax & 0xFF00) | 0x01;
            set_cf(u, true);
            break;
    }

    reg16_write(u, UC_X86_REG_AX, ax);
    reg16_write(u, UC_X86_REG_BX, bx);
    reg16_write(u, UC_X86_REG_CX, cx);
    reg16_write(u, UC_X86_REG_DX, dx);
}

static void handle_int12(uc_engine *u)
{
    reg16_write(u, UC_X86_REG_AX, 640);
}

static void handle_int11(uc_engine *u)
{
    reg16_write(u, UC_X86_REG_AX, 0x0044);
}

static void handle_int15(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);
    uint8_t ah = ax >> 8;

    switch (ah) {

        case 0x88:
            ax = 0;
            reg16_write(u, UC_X86_REG_AX, ax);
            break;

        case 0xC0:
            ax = (ax & 0x00FF) | (0x86 << 8);
            reg16_write(u, UC_X86_REG_AX, ax);
            set_cf(u, true);
            break;

        case 0x24:
            ax = (ax & 0x00FF);
            reg16_write(u, UC_X86_REG_AX, ax);
            set_cf(u, false);
            break;

        case 0x41:
            SDL_Delay(1);
            set_cf(u, false);
            break;

        case 0x86:
            SDL_Delay(1);
            set_cf(u, false);
            break;

        default:
            set_cf(u, true);
            break;
    }
}

static void handle_int1a(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);
    uint8_t ah = ax >> 8;

    switch (ah) {

        case 0x00: {
            uint64_t secs = time(NULL) % 86400;
            uint64_t ticks = (secs * 182) / 10;

            reg16_write(u, UC_X86_REG_CX, ticks >> 16);
            reg16_write(u, UC_X86_REG_DX, ticks & 0xFFFF);

            ax = (ax & 0xFF00) | 0;
            reg16_write(u, UC_X86_REG_AX, ax);
            break;
        }

        case 0x01:
            break;

        case 0x02:
        case 0x03:
            reg16_write(u, UC_X86_REG_CX, 0);
            reg16_write(u, UC_X86_REG_DX, 0);
            set_cf(u, false);
            break;

        case 0x04: {
            time_t now = time(NULL);
            struct tm *tm = localtime(&now);

            uint16_t year = tm->tm_year + 1900;
            uint8_t century = year / 100;
            uint8_t yr = year % 100;

            reg16_write(u, UC_X86_REG_CX, (century << 8) | yr);
            reg16_write(u, UC_X86_REG_DX, ((tm->tm_mon + 1) << 8) | tm->tm_mday);
            set_cf(u, false);
            break;
        }

        case 0x05:
            set_cf(u, false);
            break;

        default:
            set_cf(u, true);
            break;
    }
}

static void handle_int2f(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);

    switch (ax) {

        case 0x1600:
            ax = (ax & 0xFF00) | 0;
            reg16_write(u, UC_X86_REG_AX, ax);
            break;

        case 0x1680:
            ax = (ax & 0xFF00) | 0;
            reg16_write(u, UC_X86_REG_AX, ax);
            break;

        case 0x4A01:
        case 0x4A02:
            ax = 0;
            reg16_write(u, UC_X86_REG_AX, ax);
            set_cf(u, false);
            break;

        default:
            break;
    }
}

static void handle_int21(uc_engine *u)
{
    uint16_t ax = reg16_read(u, UC_X86_REG_AX);
    uint16_t bx = reg16_read(u, UC_X86_REG_BX);
    uint16_t cx = reg16_read(u, UC_X86_REG_CX);
    uint16_t dx = reg16_read(u, UC_X86_REG_DX);
    uint16_t si = reg16_read(u, UC_X86_REG_SI);
    uint16_t di = reg16_read(u, UC_X86_REG_DI);
    uint16_t ds = reg16_read(u, UC_X86_REG_DS);
    uint16_t es = reg16_read(u, UC_X86_REG_ES);

    uint8_t ah = ax >> 8;
    uint8_t al = ax & 0xFF;

    switch (ah) {

        /* Terminate */
        case 0x00:
            stop_emulation(u);
            return;

            /* Read char with echo */
            case 0x01: {
                uint8_t c = wait_ascii_key(u);

                if (!emu_running)
                    return;

                if (c == 3) {
                    stop_emulation(u);
                    return;
                }

                video_putc(u, c, 0x07);
                ax = (ax & 0xFF00) | c;
                break;
            }

            /* Write char */
            case 0x02:
                video_putc(u, dx & 0xFF, 0x07);
                ax = (ax & 0xFF00) | (dx & 0xFF);
                break;

                /* Read char from STDAUX */
                case 0x03:
                    ax = (ax & 0xFF00) | 0;
                    break;

                    /* Write char to STDAUX */
                    case 0x04:
                        break;

                        /* Write char to STDPRN */
                        case 0x05:
                            break;

                            /* Direct console I/O */
                            case 0x06: {
                                if ((dx & 0xFF) == 0xFF) {
                                    if (!key_empty()) {
                                        uint16_t k = key_peek();

                                        if ((k & 0xFF) != 0) {
                                            key_pop();
                                            ax = (ax & 0xFF00) | (k & 0xFF);
                                            set_zf(u, false);
                                        } else {
                                            ax &= 0xFF00;
                                            set_zf(u, true);
                                        }
                                    } else {
                                        ax &= 0xFF00;
                                        set_zf(u, true);
                                    }
                                } else {
                                    video_putc(u, dx & 0xFF, 0x07);
                                    ax = (ax & 0xFF00) | (dx & 0xFF);
                                }

                                break;
                            }

                            /* Direct input no echo */
                            case 0x07:
                            case 0x08: {
                                uint8_t c = wait_ascii_key(u);

                                if (!emu_running)
                                    return;

                                if (c == 3) {
                                    stop_emulation(u);
                                    return;
                                }

                                ax = (ax & 0xFF00) | c;
                                break;
                            }

                            /* Print string */
                            case 0x09: {
                                uint32_t addr = seg_off_to_linear(ds, dx);

                                for (int i = 0; i < 65536; i++) {
                                    uint8_t c = 0;
                                    if (uc_mem_read(u, addr + i, &c, 1) != UC_ERR_OK)
                                        break;

                                    if (c == '$')
                                        break;

                                    video_putc(u, c, 0x07);
                                }

                                break;
                            }

                            /* Buffered input */
                            case 0x0A: {
                                uint32_t addr = seg_off_to_linear(ds, dx);

                                uint8_t max = 0;
                                uc_mem_read(u, addr, &max, 1);

                                uint8_t count = 0;

                                while (count < max) {
                                    uint8_t c = wait_ascii_key(u);

                                    if (!emu_running)
                                        return;

                                    if (c == 3) {
                                        stop_emulation(u);
                                        return;
                                    }

                                    if (c == 13)
                                        break;

                                    if (c == 8) {
                                        if (count > 0) {
                                            count--;
                                            video_putc(u, 8, 0x07);
                                        }
                                        continue;
                                    }

                                    uc_mem_write(u, addr + 2 + count, &c, 1);
                                    count++;
                                    video_putc(u, c, 0x07);
                                }

                                uc_mem_write(u, addr + 1, &count, 1);
                                ax = (ax & 0xFF00) | 0x0D;
                                break;
                            }

                            /* Input status */
                            case 0x0B:
                                ax = (ax & 0xFF00) | (!key_empty() ? 0xFF : 0x00);
                                break;

                                /* Flush input buffer then input */
                                case 0x0C: {
                                    key_clear();

                                    if (al == 0x01 || al == 0x06 || al == 0x07 || al == 0x08) {
                                        uint8_t c = wait_ascii_key(u);

                                        if (!emu_running)
                                            return;

                                        ax = (ax & 0xFF00) | c;
                                    } else if (al == 0x0A) {
                                        uint32_t addr = seg_off_to_linear(ds, dx);
                                        uint8_t max = 0;
                                        uint8_t count = 0;

                                        uc_mem_read(u, addr, &max, 1);

                                        while (count < max) {
                                            uint8_t c = wait_ascii_key(u);

                                            if (!emu_running)
                                                return;

                                            if (c == 13)
                                                break;

                                            if (c == 8) {
                                                if (count > 0) {
                                                    count--;
                                                    video_putc(u, 8, 0x07);
                                                }
                                                continue;
                                            }

                                            uc_mem_write(u, addr + 2 + count, &c, 1);
                                            count++;
                                            video_putc(u, c, 0x07);
                                        }

                                        uc_mem_write(u, addr + 1, &count, 1);
                                        ax = (ax & 0xFF00) | 0x0D;
                                    }

                                    break;
                                }

                                /* Reset drive */
                                case 0x0D:
                                    break;

                                    /* Select drive */
                                    case 0x0E:
                                        ax = (ax & 0xFF00) | 26;
                                        break;

                                        /* FCB open */
                                        case 0x0F:
                                            ax = (ax & 0xFF00) | 0xFF;
                                            set_cf(u, true);
                                            break;

                                            /* FCB close */
                                            case 0x10:
                                                ax = (ax & 0xFF00) | 0xFF;
                                                set_cf(u, true);
                                                break;

                                                /* FCB find first */
                                                case 0x11:
                                                    ax = (ax & 0xFF00) | 0xFF;
                                                    set_cf(u, true);
                                                    break;

                                                    /* FCB find next */
                                                    case 0x12:
                                                        ax = (ax & 0xFF00) | 0xFF;
                                                        set_cf(u, true);
                                                        break;

                                                        /* FCB delete */
                                                        case 0x13:
                                                            ax = (ax & 0xFF00) | 0xFF;
                                                            set_cf(u, true);
                                                            break;

                                                            /* FCB read */
                                                            case 0x14:
                                                                ax = (ax & 0xFF00) | 0xFF;
                                                                set_cf(u, true);
                                                                break;

                                                                /* FCB write */
                                                                case 0x15:
                                                                    ax = (ax & 0xFF00) | 0xFF;
                                                                    set_cf(u, true);
                                                                    break;

                                                                    /* FCB create */
                                                                    case 0x16:
                                                                        ax = (ax & 0xFF00) | 0xFF;
                                                                        set_cf(u, true);
                                                                        break;

                                                                        /* FCB rename */
                                                                        case 0x17:
                                                                            ax = (ax & 0xFF00) | 0xFF;
                                                                            set_cf(u, true);
                                                                            break;

                                                                            /* Set DTA */
                                                                            case 0x1A:
                                                                                current_dta = seg_off_to_linear(ds, dx);
                                                                                break;

                                                                                /* Get current drive */
                                                                                case 0x19:
                                                                                    ax = (ax & 0xFF00) | 2;
                                                                                    break;

                                                                                    /* Get allocation info current drive */
                                                                                    case 0x1B:
                                                                                    case 0x1C:
                                                                                        ax = (ax & 0xFF00) | 64;
                                                                                        bx = 512;
                                                                                        cx = 64;
                                                                                        dx = 0x7FFF;
                                                                                        break;

                                                                                        /* FCB random read */
                                                                                        case 0x21:
                                                                                        case 0x22:
                                                                                        case 0x23:
                                                                                        case 0x24:
                                                                                        case 0x27:
                                                                                        case 0x28:
                                                                                            ax = (ax & 0xFF00) | 0xFF;
                                                                                            set_cf(u, true);
                                                                                            break;

                                                                                            /* Set interrupt vector */
                                                                                            case 0x25: {
                                                                                                uint8_t n = al;
                                                                                                uint32_t ivt = n * 4;

                                                                                                uint16_t off = dx;
                                                                                                uint16_t seg = ds;

                                                                                                uc_mem_write(u, ivt + 0, &off, 2);
                                                                                                uc_mem_write(u, ivt + 2, &seg, 2);
                                                                                                break;
                                                                                            }

                                                                                            /* Create PSP */
                                                                                            case 0x26:
                                                                                                break;

                                                                                                /* Get date */
                                                                                                case 0x2A: {
                                                                                                    time_t now = time(NULL);
                                                                                                    struct tm *tm = localtime(&now);

                                                                                                    cx = tm->tm_year + 1900;
                                                                                                    dx = ((tm->tm_mon + 1) << 8) | tm->tm_mday;
                                                                                                    ax = (ax & 0xFF00) | tm->tm_wday;
                                                                                                    break;
                                                                                                }

                                                                                                /* Set date */
                                                                                                case 0x2B:
                                                                                                    ax = 0;
                                                                                                    break;

                                                                                                    /* Get time */
                                                                                                    case 0x2C: {
                                                                                                        time_t now = time(NULL);
                                                                                                        struct tm *tm = localtime(&now);

                                                                                                        cx = (tm->tm_hour << 8) | tm->tm_min;
                                                                                                        dx = (tm->tm_sec << 8) | 0;
                                                                                                        break;
                                                                                                    }

                                                                                                    /* Set time */
                                                                                                    case 0x2D:
                                                                                                        ax = 0;
                                                                                                        break;

                                                                                                        /* Set verify flag */
                                                                                                        case 0x2E:
                                                                                                            break;

                                                                                                            /* Get DTA */
                                                                                                            case 0x2F:
                                                                                                                es = current_dta >> 4;
                                                                                                                bx = current_dta & 0xF;
                                                                                                                reg16_write(u, UC_X86_REG_ES, es);
                                                                                                                break;

                                                                                                                /* DOS version */
                                                                                                                case 0x30:
                                                                                                                    ax = 0x0005;
                                                                                                                    break;

                                                                                                                    /* Terminate and stay resident */
                                                                                                                    case 0x31:
                                                                                                                        stop_emulation(u);
                                                                                                                        return;

                                                                                                                        /* Get DPB */
                                                                                                                        case 0x32:
                                                                                                                            ax = (ax & 0xFF00) | 0xFF;
                                                                                                                            set_cf(u, true);
                                                                                                                            break;

                                                                                                                            /* Ctrl-Break / boot drive */
                                                                                                                            case 0x33: {
                                                                                                                                switch (al) {
                                                                                                                                    case 0x00:
                                                                                                                                        dx = ctrl_break_enabled ? 1 : 0;
                                                                                                                                        break;
                                                                                                                                    case 0x01:
                                                                                                                                        ctrl_break_enabled = (dx != 0);
                                                                                                                                        break;
                                                                                                                                    case 0x02: {
                                                                                                                                        uint16_t old = ctrl_break_enabled ? 1 : 0;
                                                                                                                                        dx = old;
                                                                                                                                        ctrl_break_enabled = ((bx & 0xFF) != 0);
                                                                                                                                        break;
                                                                                                                                    }
                                                                                                                                    case 0x05:
                                                                                                                                        dx = 3;
                                                                                                                                        break;
                                                                                                                                    case 0x06:
                                                                                                                                        ax = 0x0005;
                                                                                                                                        break;
                                                                                                                                    default:
                                                                                                                                        break;
                                                                                                                                }
                                                                                                                                break;
                                                                                                                            }

                                                                                                                            /* InDOS flag */
                                                                                                                            case 0x34: {
                                                                                                                                uint8_t indos = 0;
                                                                                                                                uc_mem_write(u, 0x500, &indos, 1);

                                                                                                                                es = 0;
                                                                                                                                bx = 0x500;
                                                                                                                                reg16_write(u, UC_X86_REG_ES, es);
                                                                                                                                break;
                                                                                                                            }

                                                                                                                            /* Get interrupt vector */
                                                                                                                            case 0x35: {
                                                                                                                                uint8_t n = al;
                                                                                                                                uint32_t ivt = n * 4;

                                                                                                                                uint16_t off = 0;
                                                                                                                                uint16_t seg = 0;

                                                                                                                                uc_mem_read(u, ivt + 0, &off, 2);
                                                                                                                                uc_mem_read(u, ivt + 2, &seg, 2);

                                                                                                                                bx = off;
                                                                                                                                reg16_write(u, UC_X86_REG_ES, seg);
                                                                                                                                break;
                                                                                                                            }

                                                                                                                            /* Disk free space */
                                                                                                                            case 0x36:
                                                                                                                                ax = 64;
                                                                                                                                bx = 0x7FFF;
                                                                                                                                cx = 512;
                                                                                                                                dx = 0x7FFF;
                                                                                                                                break;

                                                                                                                                /* Switch character */
                                                                                                                                case 0x37:
                                                                                                                                    if (al == 0 || al == 2)
                                                                                                                                        dx = '/';
        break;

        /* Country info */
        case 0x38: {
            static uint8_t country[34] = {
                1, 0, '$', 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            };

            uc_mem_write(u, 0x700, country, sizeof(country));

            if (al == 0xFF) {
                es = 0;
                bx = 0x700;
                reg16_write(u, UC_X86_REG_ES, es);
            } else {
                bx = 1;
                ax = 1;
            }

            break;
        }

        /* mkdir */
        case 0x39: {
            char host[512];

            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                break;
            }

            if (mkdir(host, 0755) == 0)
                dos_success(u);
            else
                dos_error(u, DOS_ERR_PATH_NOT_FOUND);

            break;
        }

        /* rmdir */
        case 0x3A: {
            char host[512];

            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                break;
            }

            if (rmdir(host) == 0)
                dos_success(u);
            else
                dos_error(u, DOS_ERR_ACCESS_DENIED);

            break;
        }

        /* chdir */
        case 0x3B: {
            char host[512];

            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                break;
            }

            if (chdir(host) == 0)
                dos_success(u);
            else
                dos_error(u, DOS_ERR_PATH_NOT_FOUND);

            break;
        }

        /* create file */
        case 0x3C: {
            char host[512];

            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                break;
            }

            int fd = open(host, O_RDWR | O_CREAT | O_TRUNC, 0644);
            if (fd < 0) {
                dos_error(u, DOS_ERR_ACCESS_DENIED);
                break;
            }

            int h = alloc_dos_handle(fd);
            if (h < 0) {
                dos_error(u, DOS_ERR_TOO_MANY_FILES);
                break;
            }

            ax = h;
            bx = h;
            dos_success(u);
            break;
        }

        /* open file */
        case 0x3D: {
            char host[512];

            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                break;
            }

            int flags;

            switch (al & 3) {
                case 0:
                    flags = O_RDONLY;
                    break;
                case 1:
                    flags = O_WRONLY;
                    break;
                default:
                    flags = O_RDWR;
                    break;
            }

            int fd = open(host, flags);
            if (fd < 0) {
                dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                break;
            }

            int h = alloc_dos_handle(fd);
            if (h < 0) {
                dos_error(u, DOS_ERR_TOO_MANY_FILES);
                break;
            }

            ax = h;
            bx = h;
            dos_success(u);
            break;
        }

        /* close file */
        case 0x3E: {
            if (bx < 3) {
                dos_success(u);
                break;
            }

            if (!valid_handle(bx)) {
                dos_error(u, DOS_ERR_INVALID_HANDLE);
                break;
            }

            close(dos_handles[bx]);
            dos_handles[bx] = -1;
            dos_success(u);
            break;
        }

        /* read file */
        case 0x3F: {
            if (!valid_handle(bx)) {
                dos_error(u, DOS_ERR_INVALID_HANDLE);
                break;
            }

            if (cx == 0) {
                ax = 0;
                dos_success(u);
                break;
            }

            uint32_t addr = seg_off_to_linear(ds, dx);

            if (bx == 0) {
                uint8_t c = wait_ascii_key(u);

                if (!emu_running)
                    return;

                uc_mem_write(u, addr, &c, 1);
                ax = 1;
                dos_success(u);
                break;
            }

            uint8_t *tmp = malloc(cx);
            if (!tmp) {
                dos_error(u, DOS_ERR_NO_MEMORY);
                break;
            }

            ssize_t n = read(dos_handles[bx], tmp, cx);
            if (n < 0)
                n = 0;

            if (n > 0)
                uc_mem_write(u, addr, tmp, n);

            ax = (uint16_t)n;
            free(tmp);

            dos_success(u);
            break;
        }

        /* write file */
        case 0x40: {
            if (!valid_handle(bx)) {
                dos_error(u, DOS_ERR_INVALID_HANDLE);
                break;
            }

            if (cx == 0) {
                ax = 0;
                dos_success(u);
                break;
            }

            uint32_t addr = seg_off_to_linear(ds, dx);

            if (bx == 1 || bx == 2) {
                for (uint32_t i = 0; i < cx; i++) {
                    uint8_t c = 0;
                    uc_mem_read(u, addr + i, &c, 1);
                    video_putc(u, c, 0x07);
                }

                ax = cx;
                dos_success(u);
                break;
            }

            uint8_t *tmp = malloc(cx);
            if (!tmp) {
                dos_error(u, DOS_ERR_NO_MEMORY);
                break;
            }

            if (uc_mem_read(u, addr, tmp, cx) != UC_ERR_OK) {
                free(tmp);
                dos_error(u, DOS_ERR_ACCESS_DENIED);
                break;
            }

            ssize_t n = write(dos_handles[bx], tmp, cx);
            if (n < 0)
                n = 0;

            ax = (uint16_t)n;
            free(tmp);

            dos_success(u);
            break;
        }

        /* delete file */
        case 0x41: {
            char host[512];

            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                break;
            }

            if (unlink(host) == 0)
                dos_success(u);
            else
                dos_error(u, DOS_ERR_FILE_NOT_FOUND);

            break;
        }

        /* lseek - FIXED: whence initialization bug */
        case 0x42: {
            if (!valid_handle(bx)) {
                dos_error(u, DOS_ERR_INVALID_HANDLE);
                break;
            }

            int whence;

            if (al == 0) whence = SEEK_SET;
            else if (al == 1) whence = SEEK_CUR;
            else if (al == 2) whence = SEEK_END;
            else {
                dos_error(u, DOS_ERR_INVALID_FUNC);
                break;
            }

            off_t offset = ((off_t)cx << 16) | dx;
            off_t res = lseek(dos_handles[bx], offset, whence);

            if (res < 0)
                dos_error(u, DOS_ERR_INVALID_HANDLE);
            else {
                ax = res & 0xFFFF;
                dx = (res >> 16) & 0xFFFF;
                dos_success(u);
            }

            break;
        }

        /* get/set file attributes */
        case 0x43: {
            char host[512];

            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                break;
            }

            if (al == 0) {
                struct stat st;

                if (stat(host, &st) != 0) {
                    dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                    break;
                }

                uint16_t attr = 0;

                if (S_ISDIR(st.st_mode))
                    attr |= 0x10;

                if (!(st.st_mode & S_IWUSR))
                    attr |= 0x01;

                cx = attr;
                dos_success(u);
            } else if (al == 1) {
                mode_t mode = 0644;

                if (cx & 1)
                    mode = 0444;

                if (chmod(host, mode) == 0)
                    dos_success(u);
                else
                    dos_error(u, DOS_ERR_ACCESS_DENIED);
            }

            break;
        }

        /* IOCTL */
        case 0x44: {
            switch (al) {

                case 0x00:
                    if (!valid_handle(bx)) {
                        dos_error(u, DOS_ERR_INVALID_HANDLE);
                        break;
                    }

                    dx = (bx <= 2) ? 0x80D3 : 0;
                    dos_success(u);
                    break;

                case 0x01:
                    dos_success(u);
                    break;

                case 0x02:
                case 0x03:
                    ax = 0;
                    dos_success(u);
                    break;

                case 0x04:
                case 0x05:
                    dos_success(u);
                    break;

                case 0x06:
                    if (bx == 0)
                        ax = (!key_empty()) ? 0xFF : 0x00;
                else
                    ax = 0xFF;
                break;

                case 0x07:
                    ax = 0xFF;
                    break;

                case 0x08:
                case 0x09:
                case 0x0A:
                    ax = 0;
                    dos_success(u);
                    break;

                case 0x0B:
                    dos_success(u);
                    break;

                case 0x0C:
                case 0x0D:
                case 0x0E:
                case 0x0F:
                    dos_success(u);
                    break;

                default:
                    dos_error(u, DOS_ERR_INVALID_FUNC);
                    break;
            }

            break;
        }

        /* dup handle */
        case 0x45: {
            if (!valid_handle(bx)) {
                dos_error(u, DOS_ERR_INVALID_HANDLE);
                break;
            }

            int fd = dup(dos_handles[bx]);
            if (fd < 0) {
                dos_error(u, DOS_ERR_TOO_MANY_FILES);
                break;
            }

            int h = alloc_dos_handle(fd);
            if (h < 0) {
                dos_error(u, DOS_ERR_TOO_MANY_FILES);
                break;
            }

            ax = h;
            bx = h;
            dos_success(u);
            break;
        }

        /* force dup handle */
        case 0x46: {
            if (!valid_handle(bx) || cx >= max_dos_handles) {
                dos_error(u, DOS_ERR_INVALID_HANDLE);
                break;
            }

            int fd = dup(dos_handles[bx]);
            if (fd < 0) {
                dos_error(u, DOS_ERR_TOO_MANY_FILES);
                break;
            }

            if (cx > 2 && dos_handles[cx] >= 0)
                close(dos_handles[cx]);

            dos_handles[cx] = fd;
            dos_success(u);
            break;
        }

        /* get current directory */
        case 0x47: {
            char cwd[512];

            if (getcwd(cwd, sizeof(cwd)) == NULL) {
                dos_error(u, DOS_ERR_INVALID_DRIVE);
                break;
            }

            char out[512];
            size_t j = 0;

            const char *p = cwd;
            if (*p == '/')
                p++;

            while (*p && j + 1 < sizeof(out)) {
                char c = *p++;
                if (c == '/')
                    c = '\\';
                out[j++] = c;
            }

            out[j] = 0;

            uint32_t addr = seg_off_to_linear(ds, si);
            guest_write_cstring(u, addr, out, 63);

            dos_success(u);
            break;
        }

        /* allocate memory */
        case 0x48: {
            uint16_t paras = bx;
            if (paras == 0)
                paras = 1;

            if (alloc_seg + paras > 0x9FFF) {
                ax = 8;
                bx = 0x9FFF - alloc_seg;
                set_cf(u, true);
            } else {
                ax = alloc_seg;
                alloc_seg += paras;
                dos_success(u);
            }

            break;
        }

        /* free memory */
        case 0x49:
            dos_success(u);
            break;

            /* resize memory */
            case 0x4A:
                dos_success(u);
                break;

                /* execute program (EXEC) */
                case 0x4B: {
                    char host[512];

                    if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                        dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                        break;
                    }

                    if (access(host, F_OK) != 0) {
                        dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                        break;
                    }

                    dos_error(u, DOS_ERR_NO_MEMORY);
                    break;
                }

                /* exit */
                case 0x4C:
                    stop_emulation(u);
                    return;

                    /* return code */
                    case 0x4D:
                        ax = 0;
                        break;

                        /* find first */
                        case 0x4E: {
                            char host[512];

                            if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                                dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                                break;
                            }

                            if (find_dir) {
                                closedir(find_dir);
                                find_dir = NULL;
                            }

                            split_path(host, find_dirpath, sizeof(find_dirpath), find_pattern, sizeof(find_pattern));

                            find_dir = opendir(find_dirpath);
                            if (!find_dir) {
                                dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                                break;
                            }

                            char name[13];
                            uint8_t attr;
                            uint16_t date, time;
                            uint32_t size;

                            if (find_next_entry(name, &attr, &date, &time, &size)) {
                                write_find_result(u, current_dta, name, attr, date, time, size);
                                dos_success(u);
                            } else {
                                closedir(find_dir);
                                find_dir = NULL;
                                dos_error(u, DOS_ERR_NO_MORE_FILES);
                            }

                            break;
                        }

                        /* find next */
                        case 0x4F: {
                            if (!find_dir) {
                                dos_error(u, DOS_ERR_NO_MORE_FILES);
                                break;
                            }

                            char name[13];
                            uint8_t attr;
                            uint16_t date, time;
                            uint32_t size;

                            if (find_next_entry(name, &attr, &date, &time, &size)) {
                                write_find_result(u, current_dta, name, attr, date, time, size);
                                dos_success(u);
                            } else {
                                closedir(find_dir);
                                find_dir = NULL;
                                dos_error(u, DOS_ERR_NO_MORE_FILES);
                            }

                            break;
                        }

                        /* set PSP */
                        case 0x50:
                            current_psp_seg = bx;
                            break;

                            /* get PSP */
                            case 0x51:
                                bx = current_psp_seg;
                                break;

                                /* list of lists */
                                case 0x52: {
                                    uint8_t lol[32];
                                    memset(lol, 0, sizeof(lol));
                                    uc_mem_write(u, 0x600, lol, sizeof(lol));

                                    es = 0;
                                    bx = 0x600;
                                    reg16_write(u, UC_X86_REG_ES, es);
                                    break;
                                }

                                /* Translate BPB to DPB */
                                case 0x53:
                                    dos_success(u);
                                    break;

                                    /* verify flag */
                                    case 0x54:
                                        ax = (ax & 0xFF00) | 0;
                                        break;

                                        /* rename file */
                                        case 0x56: {
                                            char oldp[512];
                                            char newp[512];

                                            if (read_dos_path(u, ds, dx, oldp, sizeof(oldp)) != 0 ||
                                                read_dos_path(u, es, di, newp, sizeof(newp)) != 0) {
                                                dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                                            break;
                                                }

                                                if (rename(oldp, newp) == 0)
                                                    dos_success(u);
                                            else
                                                dos_error(u, DOS_ERR_ACCESS_DENIED);

                                            break;
                                        }

                                        /* get/set file date-time */
                                        case 0x57: {
                                            if (al == 0) {
                                                if (!valid_handle(bx)) {
                                                    dos_error(u, DOS_ERR_INVALID_HANDLE);
                                                    break;
                                                }

                                                struct stat st;

                                                if (fstat(dos_handles[bx], &st) != 0) {
                                                    dos_error(u, DOS_ERR_INVALID_HANDLE);
                                                    break;
                                                }

                                                uint16_t date, time;
                                                unix_to_dos_datetime(st.st_mtime, &date, &time);

                                                cx = time;
                                                dx = date;
                                                dos_success(u);
                                            } else if (al == 1) {
                                                dos_success(u);
                                            }

                                            break;
                                        }

                                        /* allocation strategy */
                                        case 0x58:
                                            if (al == 0)
                                                ax = 0;
        dos_success(u);
        break;

        /* extended error */
        case 0x59:
            ax = 0;
            bx = 0;
            cx = 0;
            dx = 0;
            si = 0;
            di = 0;
            es = 0;
            reg16_write(u, UC_X86_REG_ES, es);
            dos_success(u);
            break;

            /* create unique file */
            case 0x5A: {
                char host[512];

                if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                    dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                    break;
                }

                char full[1024];
                snprintf(full, sizeof(full), "%s/DOS%04X.TMP", host, getpid() & 0xFFFF);

                int fd = open(full, O_RDWR | O_CREAT | O_EXCL, 0644);
                if (fd < 0) {
                    dos_error(u, DOS_ERR_ACCESS_DENIED);
                    break;
                }

                int h = alloc_dos_handle(fd);
                if (h < 0) {
                    dos_error(u, DOS_ERR_TOO_MANY_FILES);
                    break;
                }

                char dosfull[1024];
                size_t j = 0;

                for (size_t i = 0; full[i] && j + 1 < sizeof(dosfull); i++) {
                    char c = full[i];
                    if (c == '/')
                        c = '\\';
                    dosfull[j++] = c;
                }

                dosfull[j] = 0;

                guest_write_cstring(u, seg_off_to_linear(ds, dx), dosfull, 63);

                ax = h;
                bx = h;
                dos_success(u);
                break;
            }

            /* create new file */
            case 0x5B: {
                char host[512];

                if (read_dos_path(u, ds, dx, host, sizeof(host)) != 0) {
                    dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                    break;
                }

                int fd = open(host, O_RDWR | O_CREAT | O_EXCL, 0644);
                if (fd < 0) {
                    dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                    break;
                }

                int h = alloc_dos_handle(fd);
                if (h < 0) {
                    dos_error(u, DOS_ERR_TOO_MANY_FILES);
                    break;
                }

                ax = h;
                bx = h;
                dos_success(u);
                break;
            }

            /* lock/unlock file */
            case 0x5C:
                dos_success(u);
                break;

                /* server function call */
                case 0x5D:
                    dos_error(u, DOS_ERR_INVALID_FUNC);
                    break;

                    /* Get/set drive error table */
                    case 0x5E:
                    case 0x5F:
                        dos_error(u, DOS_ERR_INVALID_FUNC);
                        break;

                        /* canonicalize path */
                        case 0x60: {
                            uint32_t src = seg_off_to_linear(ds, si);
                            uint32_t dst = seg_off_to_linear(es, di);

                            char guest[512];

                            if (guest_read_cstring(u, src, guest, sizeof(guest)) != 0) {
                                ax = 0x5A;
                                set_cf(u, true);
                                break;
                            }

                            char out[512];
                            size_t j = 0;

                            for (size_t i = 0; guest[i] && j + 1 < sizeof(out); i++) {
                                char c = guest[i];

                                if (c == '/')
                                    c = '\\';

                                out[j++] = (char)toupper((unsigned char)c);
                            }

                            out[j] = 0;

                            guest_write_cstring(u, dst, out, 63);
                            dos_success(u);
                            break;
                        }

                        /* get PSP address */
                        case 0x62:
                            bx = current_psp_seg;
                            break;

                            /* get lead byte table */
                            case 0x63:
                                dos_error(u, DOS_ERR_INVALID_FUNC);
                                break;

                                /* code page */
                                case 0x66:
                                    if (al == 1) {
                                        bx = 437;
                                        dx = 437;
                                    }
                                    dos_success(u);
                                    break;

                                    /* set handle count */
                                    case 0x67:
                                        if (cx > 0 && cx <= 255)
                                            max_dos_handles = cx;
        dos_success(u);
        break;

        /* commit file */
        case 0x68:
        case 0x6A:
            if (valid_handle(bx))
                fsync(dos_handles[bx]);
        dos_success(u);
        break;

        /* commit and close */
        case 0x6B:
            if (valid_handle(bx)) {
                fsync(dos_handles[bx]);
                close(dos_handles[bx]);
                dos_handles[bx] = -1;
            }
            dos_success(u);
            break;

            /* extended open/create */
            case 0x6C: {
                char host[512];

                if (read_dos_path(u, ds, si, host, sizeof(host)) != 0) {
                    dos_error(u, DOS_ERR_PATH_NOT_FOUND);
                    break;
                }

                int flags = 0;

                switch (bx & 3) {
                    case 0:
                        flags = O_RDONLY;
                        break;
                    case 1:
                        flags = O_WRONLY;
                        break;
                    default:
                        flags = O_RDWR;
                        break;
                }

                uint8_t action = dx & 0x0F;

                if (action == 1 || action == 3)
                    flags |= O_TRUNC;

                if (action >= 2)
                    flags |= O_CREAT;

                int fd = open(host, flags, 0644);
                if (fd < 0) {
                    dos_error(u, DOS_ERR_FILE_NOT_FOUND);
                    break;
                }

                int h = alloc_dos_handle(fd);
                if (h < 0) {
                    dos_error(u, DOS_ERR_TOO_MANY_FILES);
                    break;
                }

                ax = h;
                cx = 1;
                dos_success(u);
                break;
            }

            /* Long filename functions (Windows 95+) */
            case 0x71:
                dos_error(u, DOS_ERR_INVALID_FUNC);
                break;

            default:
                break;
    }

    reg16_write(u, UC_X86_REG_AX, ax);
    reg16_write(u, UC_X86_REG_BX, bx);
    reg16_write(u, UC_X86_REG_CX, cx);
    reg16_write(u, UC_X86_REG_DX, dx);
    reg16_write(u, UC_X86_REG_SI, si);
    reg16_write(u, UC_X86_REG_DI, di);
}

static void hook_interrupt(uc_engine *u, uint32_t intno, void *user_data)
{
    (void)user_data;

    switch (intno) {

        case 0x10:
            handle_int10(u);
            advance_ip(u, 2);
            break;

        case 0x11:
            handle_int11(u);
            advance_ip(u, 2);
            break;

        case 0x12:
            handle_int12(u);
            advance_ip(u, 2);
            break;

        case 0x13:
            handle_int13(u);
            advance_ip(u, 2);
            break;

        case 0x15:
            handle_int15(u);
            advance_ip(u, 2);
            break;

        case 0x16:
            handle_int16(u);
            advance_ip(u, 2);
            break;

        case 0x1A:
            handle_int1a(u);
            advance_ip(u, 2);
            break;

        case 0x20:
            stop_emulation(u);
            break;

        case 0x21:
            handle_int21(u);

            if (!emu_running)
                return;

        advance_ip(u, 2);
        break;

        case 0x2F:
            handle_int2f(u);
            advance_ip(u, 2);
            break;

        case 0x33:
            handle_int33(u);
            advance_ip(u, 2);
            break;

        case 3:
            advance_ip(u, 1);
            break;

        default:
            advance_ip(u, 2);
            break;
    }

    if (emu_running) {
        uc_emu_stop(u);
    }
}

static void write_environment(uc_engine *u, uint16_t env_seg)
{
    static const char env[] =
    "COMSPEC=C:\\COMMAND.COM\0"
    "PATH=.\0"
    "INCLUDE=.\0"
    "LIB=.\0"
    "\0";

    uint32_t base = ((uint32_t)env_seg << 4);
    uc_mem_write(u, base, env, sizeof(env));
}

static void write_psp(uc_engine *u, uint16_t psp_seg, uint16_t env_seg, const char *cmd_tail)
{
    uint8_t psp[256];
    memset(psp, 0, sizeof(psp));

    uint32_t base = ((uint32_t)psp_seg << 4);

    psp[0x00] = 0xCD;
    psp[0x01] = 0x20;

    psp[0x02] = 0x00;
    psp[0x03] = 0xA0;

    psp[0x05] = 0xCD;
    psp[0x06] = 0x21;
    psp[0x07] = 0xCB;

    uint16_t env = env_seg;
    memcpy(psp + 0x2C, &env, 2);

    size_t len = strlen(cmd_tail);
    if (len > 126) len = 126;
    psp[0x80] = (uint8_t)len;
    if (len > 0) memcpy(psp + 0x81, cmd_tail, len);
    psp[0x81 + len] = 0x0D;

    uc_mem_write(u, base, psp, sizeof(psp));
}

static int load_com(uc_engine *u, const uint8_t *buf, long size, uint32_t *start_ip, const char *cmd_tail)
{
    if (size > 0xFF00)
        return -1;

    write_psp(u, 0, ENV_SEG, cmd_tail);
    write_environment(u, ENV_SEG);

    uc_mem_write(u, COM_LOAD_OFFSET, buf, size);

    uint16_t zero = 0;
    uint16_t sp = 0xFFFE;

    uc_mem_write(u, 0xFFFE, &zero, 2);

    reg16_write(u, UC_X86_REG_CS, zero);
    reg16_write(u, UC_X86_REG_DS, zero);
    reg16_write(u, UC_X86_REG_ES, zero);
    reg16_write(u, UC_X86_REG_SS, zero);
    reg16_write(u, UC_X86_REG_SP, sp);
    reg32_write(u, UC_X86_REG_EIP, COM_LOAD_OFFSET);

    current_psp_seg = 0;
    current_dta = 0x80;

    *start_ip = COM_LOAD_OFFSET;
    return 0;
}

static int load_mz(uc_engine *u, const uint8_t *buf, long size, uint32_t *start_ip, const char *cmd_tail)
{
    if (size < (long)sizeof(MZHeader))
        return -1;

    const MZHeader *h = (const MZHeader *)buf;

    if (h->magic != 0x5A4D)
        return -1;

    uint32_t header_size = (uint32_t)h->cparhdr * 16;

    if (header_size > (uint32_t)size)
        return -1;

    uint32_t image_size;

    if (h->cp == 0)
        image_size = 0;
    else {
        image_size = ((uint32_t)h->cp - 1) * 512;
        image_size += (h->cblp ? h->cblp : 512);
    }

    if (image_size > header_size)
        image_size -= header_size;
    else
        image_size = 0;

    if (header_size + image_size > (uint32_t)size)
        image_size = (uint32_t)size - header_size;

    uint32_t load_base = ((uint32_t)MZ_LOAD_SEG << 4);

    if (load_base + image_size > MEM_SIZE)
        image_size = MEM_SIZE - load_base;

    if (image_size > 0)
        uc_mem_write(u, load_base, buf + header_size, image_size);

    uint32_t reloc_off = h->lfarlc;

    for (int i = 0; i < h->crlc; i++) {
        uint32_t pos = reloc_off + i * 4;

        if (pos + 4 > (uint32_t)size)
            break;

        uint16_t off, seg;
        memcpy(&off, buf + pos + 0, 2);
        memcpy(&seg, buf + pos + 2, 2);

        uint32_t addr = ((uint32_t)(MZ_LOAD_SEG + seg) << 4) + off;

        if (addr + 2 <= MEM_SIZE) {
            uint16_t v = 0;
            uc_mem_read(u, addr, &v, 2);
            v += MZ_LOAD_SEG;
            uc_mem_write(u, addr, &v, 2);
        }
    }

    uint16_t psp_seg = MZ_LOAD_SEG - 0x10;

    write_psp(u, psp_seg, ENV_SEG, cmd_tail);
    write_environment(u, ENV_SEG);

    current_psp_seg = psp_seg;
    current_dta = ((uint32_t)psp_seg << 4) + 0x80;

    uint16_t cs = MZ_LOAD_SEG + h->cs;
    uint16_t ss = MZ_LOAD_SEG + h->ss;
    uint16_t ds = psp_seg;
    uint16_t es = psp_seg;

    reg16_write(u, UC_X86_REG_CS, cs);
    reg16_write(u, UC_X86_REG_SS, ss);
    reg16_write(u, UC_X86_REG_DS, ds);
    reg16_write(u, UC_X86_REG_ES, es);
    reg16_write(u, UC_X86_REG_SP, h->sp);
    reg32_write(u, UC_X86_REG_EIP, h->ip);

    *start_ip = h->ip;
    return 0;
}

static int load_program(uc_engine *u, const char *path, uint32_t *start_ip, const char *cmd_tail)
{
    FILE *f = fopen(path, "rb");
    if (!f)
        return -1;

    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);

    if (size <= 0) {
        fclose(f);
        return -1;
    }

    uint8_t *buf = malloc(size);
    if (!buf) {
        fclose(f);
        return -1;
    }

    if (fread(buf, 1, size, f) != (size_t)size) {
        fclose(f);
        free(buf);
        return -1;
    }

    fclose(f);

    int rc;

    if (size >= 2 && buf[0] == 'M' && buf[1] == 'Z')
        rc = load_mz(u, buf, size, start_ip, cmd_tail);
    else
        rc = load_com(u, buf, size, start_ip, cmd_tail);

    free(buf);
    return rc;
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s program.com|program.exe [args...]\n", argv[0]);
        return 1;
    }

    if (!sdl_init())
        return 1;

    init_dos_handles();

    char cmd_tail[128] = "";
    size_t tail_len = 0;
    for (int i = 2; i < argc; i++) {
        if (tail_len < 126) cmd_tail[tail_len++] = ' ';
        size_t arg_len = strlen(argv[i]);
        if (tail_len + arg_len < 126) {
            memcpy(cmd_tail + tail_len, argv[i], arg_len);
            tail_len += arg_len;
        } else {
            break;
        }
    }
    cmd_tail[tail_len] = '\0';

    uc_err err;

    err = uc_open(UC_ARCH_X86, UC_MODE_16, &uc);
    if (err != UC_ERR_OK) {
        fprintf(stderr, "uc_open failed: %s\n", uc_strerror(err));
        return 1;
    }

    err = uc_mem_map(uc, 0, MEM_SIZE, UC_PROT_ALL);
    if (err != UC_ERR_OK) {
        fprintf(stderr, "uc_mem_map failed: %s\n", uc_strerror(err));
        return 1;
    }

    video_init(uc);

    uint32_t start_ip = 0;

    if (load_program(uc, argv[1], &start_ip, cmd_tail) != 0) {
        fprintf(stderr, "Failed to load %s\n", argv[1]);
        return 1;
    }

    uint32_t eflags = 0x202;
    uc_reg_write(uc, UC_X86_REG_EFLAGS, &eflags);

    uc_hook hook;
    err = uc_hook_add(uc, &hook, UC_HOOK_INTR, hook_interrupt, NULL, 1, 0);
    if (err != UC_ERR_OK) {
        fprintf(stderr, "uc_hook_add failed: %s\n", uc_strerror(err));
        return 1;
    }

    while (emu_running) {
        process_sdl_events(uc);

        if (!emu_running)
            break;

        uint32_t ip = reg32_read(uc, UC_X86_REG_EIP);

        in_emulation = true;
        err = uc_emu_start(uc, ip, 0xFFFFFFFF, 2000, 20000);
        in_emulation = false;

        if (!emu_running)
            break;

        if (err != UC_ERR_OK
            #ifdef UC_ERR_TIMEOUT
            && err != UC_ERR_TIMEOUT
            #endif
        ) {
            fprintf(stderr, "uc_emu_start failed: %s\n", uc_strerror(err));
            break;
        }

        render_video(uc);
    }

    /* ADDED: Keep window open briefly after exit so it doesn't vanish instantly */
    fprintf(stdout, "\n[DOS Program Finished. Press any key or wait 3 seconds to close...]\n");
    fflush(stdout);
    Uint32 wait_start = SDL_GetTicks();
    bool wait_loop = true;
    while (wait_loop && (SDL_GetTicks() - wait_start < 3000)) {
        SDL_Event ev;
        while (SDL_PollEvent(&ev)) {
            if (ev.type == SDL_QUIT || ev.type == SDL_KEYDOWN || ev.type == SDL_MOUSEBUTTONDOWN) {
                wait_loop = false;
                break;
            }
        }
        render_video(uc);
        SDL_Delay(16);
    }

    if (find_dir)
        closedir(find_dir);

    for (int i = 3; i < max_dos_handles; i++) {
        if (dos_handles[i] >= 0)
            close(dos_handles[i]);
    }

    uc_close(uc);
    sdl_shutdown();

    return 0;
}
