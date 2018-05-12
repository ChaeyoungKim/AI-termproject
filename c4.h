

/***************************************************************************

**                                                                        **

**                          Connect-4 Algorithm                           **

**                                                                        **

**                              Version 3.11                              **

**                                                                        **

**                            By Keith Pomakis                            **

**                          (pomakis@pobox.com)                           **

**                                                                        **

**                             November, 2009                             **

**                                                                        **

****************************************************************************

**                                                                        **

**                  See the file "c4.c" for documentation.                **

**                                                                        **

****************************************************************************

**  $Id: c4.h,v 3.11 2009/11/03 14:42:07 pomakis Exp pomakis $

***************************************************************************/


#ifndef C4_DEFINED

#define C4_DEFINED


#include <time.h>

#include <stdbool.h>


#define C4_NONE      2

#define C4_MAX_LEVEL 20

#define WIDTH    7

#define HEIGHT    6

#define NUM_TO_CONNECT 4


/* See the file "c4.c" for documentation on the following functions. */


extern void    c4_poll(void(*poll_func)(void), clock_t interval);

extern void    c4_new_game(void);

extern bool    c4_make_move(int player, int column, int row);

extern bool    c4_auto_move(int player, int level, int *column, int *row);

extern char ** c4_board(void);

extern int     c4_score_of_player(int player);

extern bool    c4_is_winner(int player);

extern bool    c4_is_tie(void);

extern void    c4_win_coords(int *x1, int *y1, int *x2, int *y2);

extern void    c4_end_game(void);

extern void    c4_rule_auto_move(int player, int *column, int *row);
extern void heuristicDropOrder(int player, int* dropOrder);


//extern int rule1(int player);

extern int rule1_1(int player);

//extern int rule2(int player);

extern int rule2_1(int player);

/*extern int r12_horizontal3Check(int col, int row, int player);

extern int r12_negDiagonal3Check(int col, int row, int player);

extern int r12_posDiagonal3Check(int col, int row, int player);

extern int r12_vertical3Check(int col, int row, int player);*/

extern void r12_winning8check(int player, int * winLineArr);




extern int rule3(int player);

extern int rule4(int player);

extern int r34_diagonalCheckPos(int player, int col, int row);

extern int r34_diagonalCheckNeg(int player, int col, int row);

extern int r34_horizontalCheck(int player, int col, int row);

extern int rule5(int player, int * colArr, int min);


extern void rule6(int player, int* colArr);


extern int defaultRule(int player, int *column, int * colArr, int min);


#endif /* C4_DEFINED */



