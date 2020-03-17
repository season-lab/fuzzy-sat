#ifndef PRETTY_PRINT_H
#define PRETTY_PRINT_H

void pp_init();
void pp_set_line(int i);
void pp_set_col(int i);
void pp_print_string(int row, int col, const char* s);
void pp_printf(int row, int col, const char *format, ...);

int  pp_get_cols();
int  pp_get_rows();

#endif