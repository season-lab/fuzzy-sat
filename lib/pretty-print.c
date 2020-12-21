#include <stdio.h>
#include <assert.h>
#include <sys/ioctl.h>
#include <stdarg.h>
#include "pretty-print.h"

#define UP(n)    printf("\x1b[%dA", n)
#define DOWN(n)  printf("\x1b[%dB", n)
#define RIGHT(n) printf("\x1b[%dC", n)
#define LEFT(n)  printf("\x1b[%dD", n)

static int row_idx  = 0;
static int num_rows = 0;
static int col_idx  = 0;
static int num_cols = 0;

static inline void __clear_line() {
  int i;
  for (i = 0; i < num_cols - col_idx - 1; ++i)
    putchar(' ');

  LEFT(num_cols - col_idx);
}

static inline void __reset_cursor() {
  LEFT(col_idx);
  UP(row_idx);

  col_idx = 0;
  row_idx = 0;
}

static int __dim_changed() {
  struct winsize w;
  ioctl(0, TIOCGWINSZ, &w);

  return w.ws_row -1 != num_rows || \
    w.ws_col - 1 != num_cols;
}

void pp_init() {
  setvbuf(stdin, NULL, _IONBF, 0);
  setvbuf(stdout, NULL, _IONBF, 0);

  struct winsize w;
  ioctl(0, TIOCGWINSZ, &w);

  num_rows = w.ws_row - 1;
  num_cols = w.ws_col - 1;

  int i;
  for (i = 0; i < num_rows; ++i)
    putchar('\n');

  row_idx = num_rows;
  col_idx = 0;
  __reset_cursor();
}

void pp_set_line(int i) {
  if (row_idx - i > 0)
    UP(row_idx - i);
  else if (row_idx - i < 0)
    DOWN(i - row_idx);

  row_idx = i;
}

void pp_set_col(int i) {
  if (col_idx - i > 0)
    LEFT(col_idx - i);
  else if (col_idx - i < 0)
    RIGHT(i - col_idx);

  col_idx = i;
}

void pp_print_string(int row, int col, const char* s) {
  if (__dim_changed())
    pp_init();

  pp_set_line(row);
  pp_set_col(col);
  __clear_line();

  int j;
  for (j = 0; j < num_cols - col && s[j] != 0; ++j)
    if (s[j] != '\n') {
      putchar(s[j]);
      col_idx += 1;
    } else {
      assert (0 && "no newline allowed");
    }
  
  __reset_cursor();
}

void pp_printf(int row, int col, const char *format, ...) {
  va_list args;
  va_start(args, format);

  char var_name[512];
  int n = vsnprintf(var_name, sizeof(var_name), format, args);
  assert(n > 0 && n < sizeof(var_name) && 
    "pp_printf() - var name too long");
  
  pp_print_string(row, col, var_name);
  va_end(args);
}

int pp_get_cols() {
  return num_cols;
}

int pp_get_rows() {
  return num_rows;
}
