/***************************************************************************
**                                                                    	**
**                      	Connect-4 Algorithm                       	**
**                                                                    	**
**                          	Version 3.11                          	**
**                                                                    	**
**                        	By Keith Pomakis                        	**
**                      	(pomakis@pobox.com)                       	**
**                                                                    	**
**                         	November, 2009                         	**
**                                                                    	**
****************************************************************************
**                                                                    	**
**  This file provides the functions necessary to implement a front-end-  **
**  independent Connect-4 game.  Multiple board sizes are supported.  	**
**  It is also possible to specify the number of pieces necessary to  	**
**  connect in a row in order to win.  Therefore one can play Connect-3,  **
**  Connect-5, etc.  An efficient tree-searching algorithm (making use	**
**  of alpha-beta cutoff decisions) has been implemented to insure that   **
**  the computer plays as quickly as possible.                        	**
**                                                                    	**
**  The declaration of the public functions necessary to use this file	**
**  are contained in "c4.h".                                          	**
**                                                                    	**
**                                                                    	**
****************************************************************************
**  $Id: c4.c,v 3.11 2009/11/03 14:42:01 pomakis Exp pomakis $
***************************************************************************/

/**
* Alpha-beta cutoff 알고리즘 사용해서 시간 단축.
* c4_로 시작하는 public function들은 c4.h에 있음.
* Player의 value는 정수인데 짝수는 player 0, 홀수는 player 1임.
*/

#define _CRT_SECURE_NO_WARNINGS

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <assert.h>
#include <time.h>
#include <math.h>
#include <stdbool.h>
#include "c4.h"

/**
* 편의를 위한 매크로
*/

#define other(x)    	((x) ^ 1) // 
#define real_player(x)  ((x) & 1)

#define pop_state() (current_state = &state_stack[--depth])



/**
* 현재 상태에 대한 특정 player의 "goodness"는 자신의 score에서
* 상대방의 score를 뺀 값이다. goodness의 값이 양수라면, 해당 player가
* 자신의 상대방보다 더 나은 상황에 있다는 것을 뜻한다.
*/

#define goodness_of(player) (current_state->score[player] - current_state->score[other(player)])



/**
* Game_state 구조체는 게임의 상태를 표현.
*/

typedef struct {

	char **board;       	// 게임 보드를 표현하기 위한 이차원 배열. 열, 행이 0으로 시작. 
							// C4_NONE으로 채워지면 빈 칸, 0이면 사람, 1이면 컴퓨터.

	int *(score_array[2]);	// 각 Winning Positions에 대한 player 0과 1의 score 값을 저장한 배열
							// Player 0, 1을 한 구조체에 표현하기 위해 2차원 배열을 사용하였다.

	int score[2];       	// score_array에서 알 수 있는 각 player의 score 값
							// player x의 score 값은 score_array[x]의 모든 값의 합이다.

	short int winner;   	// 게임의 승리자 - 0, 1, 또는 무승부라면 C4_NONE
							// score_array에서도 알 수 있지만, 효율성을 위해 다른 변수를 사용.

	int num_of_pieces;  	// 현재 게임 보드 위에 놓여진 돌의 총 개수

} Game_state;



/**
* Static global variables
*/

static int size_x, size_y, total_size;
static int num_to_connect;
static int win_places;

static int ***map;  // map[x][y] win place 인덱스들로 이루어진 배열, -1로 마무리됨

static int magic_win_number;
static bool game_in_progress = false, move_in_progress = false;
static bool seed_chosen = false;
static void(*poll_function)(void) = NULL;
static clock_t poll_interval, next_poll;
static Game_state state_stack[C4_MAX_LEVEL + 1]; // 보드 21개 배열
static Game_state *current_state;
static int depth;
static int states_allocated = 0;
static int *drop_order;



/**
* A declaration of the local functions.
*/

static int num_of_win_places(int x, int y, int n);
static void update_score(int player, int x, int y);
static int drop_piece(int player, int column);
static void push_state(void);
static int evaluate(int player, int level, int alpha, int beta);
static void *emalloc(size_t size);



/**
* @function c4_poll
*
* @param (*poll_func)(void) 실행시킬 함수
* @param interval 실행될 함수의 간격
*
* interval 간격으로 첫 번째 argument의 함수를 실행한다.
* 우리는 c4_poll(print_dot, CLOCKS_PER_SEC / 2)의 모양으로 이 함수를 사용했는데,
* 이것은 0.5초 간격으로 print_dot()을 실행하라는 뜻이다.
*/

void
c4_poll(void(*poll_func)(void), clock_t interval)
{
	poll_function = poll_func;
	poll_interval = interval;
}



/**
* @function c4_new_game
*
* 새로운 게임을 시작하기 전,
* 게임 보드 크기(6*7)와 우승하기 위해 만족해야 하는 연속된 돌 수(4)를 설정한다.
* 또한, 우승 가능한 연속된 돌 위치의 모든 경우의 수를 배열로 만든다. 이
*  함수는 새로운 게임을 시작하기 위해서 필수적으로 불러야 하며,
* 한 게임이 끝나기 전 다시 부를 수 없다.
*/

void
c4_new_game() // 게임 시작!
{
	register int i, j, k, x;
	int win_index, column;
	int *win_indices;

	assert(!game_in_progress); // 괄호 안이 true면 pass, 거짓이면 진단 메시지 출력

	size_x = WIDTH;
	size_y = HEIGHT;
	total_size = WIDTH * HEIGHT;
	num_to_connect = NUM_TO_CONNECT;
	magic_win_number = 1 << num_to_connect; // magic_win_number = 16
	win_places = num_of_win_places(size_x, size_y, num_to_connect); // win_places = 69. 이길 수 있는 가능한 경우 수.

	if (!seed_chosen) { // 같은 score일 때 결정은 random으로.
		srand((unsigned int)time((time_t *)0));
		seed_chosen = true;
	}

	/* 보드 생성하기 */

	depth = 0;
	current_state = &state_stack[0]; // initial state

	current_state->board = (char **)emalloc(size_x * sizeof(char *)); // 이차원 배열 board를 위한 공간(6x7)을 마련하고 C4_NONE(=2)으로 채움.
	for (i = 0; i<size_x; i++) {
		current_state->board[i] = (char *)emalloc(size_y);
		for (j = 0; j<size_y; j++)
			current_state->board[i][j] = C4_NONE;
	}

	/* score_array 생성하기 */

	current_state->score_array[0] = (int *)emalloc(win_places * sizeof(int)); // 69개의 모든 win_places에 대해 score를 기록할 것.
	current_state->score_array[1] = (int *)emalloc(win_places * sizeof(int));
	for (i = 0; i<win_places; i++) { // 일단은 모두 1.
		current_state->score_array[0][i] = 1;
		current_state->score_array[1][i] = 1;
	}

	current_state->score[0] = current_state->score[1] = win_places; // Player 0과 1의 초기 점수 = 69.
	current_state->winner = C4_NONE;  // winner는 아직 없음.
	current_state->num_of_pieces = 0; // initial state이므로 놓인 말은 0개.

	states_allocated = 1;

	/* map 생성하기 */

	map = (int ***)emalloc(size_x * sizeof(int **)); // map은 3차원 배열. 6x7x17개 int가 들어갈 공간 할당. map[all][all][0] = -1으로 초기화.
	for (i = 0; i<size_x; i++) {
		map[i] = (int **)emalloc(size_y * sizeof(int *));
		for (j = 0; j<size_y; j++) {
			map[i][j] = (int *)emalloc((num_to_connect * 4 + 1) * sizeof(int));
			map[i][j][0] = -1;
		}
	}

	win_index = 0;

	/* Fill in the horizontal win positions */
	for (i = 0; i<size_y; i++) // i = 0~6
		for (j = 0; j<size_x - num_to_connect + 1; j++) { // j = 0~2
			for (k = 0; k<num_to_connect; k++) { // k = 0~3
				win_indices = map[j + k][i];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Fill in the vertical win positions */
	for (i = 0; i<size_x; i++)
		for (j = 0; j<size_y - num_to_connect + 1; j++) {
			for (k = 0; k<num_to_connect; k++) {
				win_indices = map[i][j + k];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Fill in the forward diagonal win positions */
	for (i = 0; i<size_y - num_to_connect + 1; i++)
		for (j = 0; j<size_x - num_to_connect + 1; j++) {
			for (k = 0; k<num_to_connect; k++) {
				win_indices = map[j + k][i + k];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Fill in the backward diagonal win positions */
	for (i = 0; i<size_y - num_to_connect + 1; i++)
		for (j = size_x - 1; j >= num_to_connect - 1; j--) {
			for (k = 0; k<num_to_connect; k++) {
				win_indices = map[j - k][i + k];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Set up the order in which automatic moves should be tried. */
	/* The columns nearer to the center of the board are usually  */
	/* better tactically and are more likely to lead to a win.	*/
	/* By ordering the search such that the central columns are   */
	/* tried first, alpha-beta cutoff is much more effective. 	*/

	drop_order = (int *)emalloc(size_x * sizeof(int));
	column = (size_x - 1) / 2;
	for (i = 1; i <= size_x; i++) {
		drop_order[i - 1] = column;
		column += ((i % 2) ? i : -i);
	}

	game_in_progress = true;
}



/**
* @function c4_make_move
*
* @param player 지금 돌을 놓을 차례인 사람(0) 또는 컴퓨터(1)
* @param column 돌을 놓을 열의 숫자
* @param row 돌을 놓을 행의 숫자
* @return 좌표가 놓을 수 없는 자리라면 false를 리턴하고,
*         성공적으로 놓았다면, true를 리턴
*
* parameter에서 입력된 사용자 (사람 또는 기계)에 해당하는 돌을
* 입력된 (row, column) 좌표에 맞게 놓는다
*/

bool
c4_make_move(int player, int column, int row)
{
	assert(game_in_progress);
	assert(!move_in_progress);

	if (column >= size_x || column < 0 || row >= size_y || row < 0 || (current_state->board[column][row] != C4_NONE))
		return false;

	int result = drop_piece(real_player(player), column);
	printf("\n * I dropped my piece on (%d, %d).\n", result + 1, column + 1);
	return (result >= 0);
}



/**
* @function c4_rule_auto_move
*
* @param player 지금 돌을 놓을 차례인 사람(0) 또는 컴퓨터(1)
* @param column 돌을 놓을 열의 좌표값을 저장하기 위해 사용되는 포인터
* @param row 돌을 놓을 행의 좌표값을 저장하기 위해 사용되는 포인터
* @return 만약 게임 보드가 꽉 차서 놓을 자리가 없다면 false를 리턴,
*         성공적으로 놓았다면, true를 리턴
*
* 컴퓨터가 Heuristic이나 Rule 중에서 무엇을 기준으로 돌을 놓을 것인가 물어보았을 때,
* Heuristic 이 선택되었다면 실행되는 함수이다.
* parameter에서 입력된 사용자(player)의 돌을 컴퓨터가 탐색트리를 level 만큼 탐색하여 돌을 놓기에 최적인 좌표를 구하고,
* 그 자리에 돌을 놓는다. 포인터 column, row에 돌을 놓은 좌표값을 저장한다.
*
* 모든 팀원이 함께 작성한 코드로, 각자 작성한 Rule들을 한 함수에서 부를 수 있도록 작성하였다.
*/

void c4_rule_auto_move(int player, int *column, int *row) {

	int check, min, i;

	check = rule1_1(player);

	if (check != -1) {
		printf(" * Rule 1 is used.\n");
		*row = drop_piece(player, check);
		*column = check;
		return;
	}

	check = rule2_1(player);

	if (check != -1) {
		printf(" * Rule 2 is used.\n");
		*row = drop_piece(player, check);
		*column = check;
		return;
	}

	int colArr[7];

	rule6(player, colArr);

	for (i = 0; i < 7; i++) {
		if (i == 0) min = colArr[i];
		else if (colArr[i] < min) min = colArr[i];
	}

	check = rule3(player);

	if (check != -1) {
		printf(" * Rule 3 is being checked.\n");
		if (colArr[check] == min) {
			printf(" * Rule 3 is used.\n");
			*row = drop_piece(player, check);
			*column = check;
			return;
		}
		printf("* Rule 3 was rejected by Rule 6.\n");
	}


	check = rule4(player);

	if (check != -1) {
		printf(" * Rule 4 is being checked.\n");
		if (colArr[check] == min) {
			printf(" * Rule 4 is used.\n");
			*row = drop_piece(player, check);
			*column = check;
			return;
		}
		printf(" * Rule 4 was rejected by Rule 6.\n");
	}


	check = rule5(player, colArr, min);

	if (check != -1) {
		printf(" * Rule 5 & 6 were used.\n");
		*row = drop_piece(player, check);
		*column = check;
		return;
	}
	else {
		*row = defaultRule(player, column, colArr, min);
		printf(" * Default rule & Rule 6 used.\n");
	}
	//printf("rule end\n");
	return;
}


/**
* @function c4_auto_move
*
* @param player 지금 돌을 놓을 차례인 사람(0) 또는 컴퓨터(1)
* @param level 탐색 트리에서 탐색할 깊이의 숫자
* @param column 돌을 놓을 열의 좌표값을 저장하기 위해 사용되는 포인터
* @param row 돌을 놓을 행의 좌표값을 저장하기 위해 사용되는 포인터
* @return 만약 게임 보드가 꽉 차서 놓을 자리가 없다면 false를 리턴,
*         성공적으로 놓았다면, true를 리턴
*
* 컴퓨터가 Heuristic이나 Rule 중에서 무엇을 기준으로 돌을 놓을 것인가 물어보았을 때,
* Heuristic 이 선택되었다면 실행되는 함수이다.
* parameter에서 입력된 사용자(player)의 돌을 컴퓨터가 탐색트리를 level 만큼 탐색하여 돌을 놓기에 최적인 좌표를 구하고,
* 그 자리에 돌을 놓는다. 포인터 column, row에 돌을 놓은 좌표값을 저장한다.
*/

bool
c4_auto_move(int player, int level, int *column, int *row)
{
	int best_column = -1, goodness = 0, best_worst = -(INT_MAX);
	int num_of_equal = 0, real_player, current_column, result, randNum;
	int choice;

	assert(game_in_progress);
	assert(!move_in_progress);
	assert(level >= 1 && level <= C4_MAX_LEVEL);

	real_player = real_player(player);

	printf(" (Heuristic : 1, Rule : 2)\n * Move choice : ");
	scanf("%d", &choice);
	printf("\n");

	if (choice == 2) {
		c4_rule_auto_move(player, column, row);
		return true;
	}

	if (current_state->num_of_pieces < 2) {
		if (current_state->num_of_pieces == 0) {
			randNum = rand() % 2;
			if (randNum == 0) {
				if (column != NULL) {
					*column = 2;
				}
				if (row != NULL) *row = 0;
				*row = drop_piece(real_player, 2);
			}
			else {
				if (column != NULL) {
					*column = 4;
				}
				if (row != NULL) *row = 0;
				*row = drop_piece(real_player, 4);
			}
		}
		else {
			if (column != NULL) {
				*column = 3;
			}
			if (row != NULL)
				*row = current_state->num_of_pieces;
			*row = drop_piece(real_player, 3);
		}
		return true;
	}

	move_in_progress = true;

	/* Simulate a drop in each of the columns and see what the results are. */

	int Hdrop_order[7];
	heuristicDropOrder(real_player, Hdrop_order);    //칼럼 별 점수를 계산해 가장 높은 칼럼 순으로 정렬여 minmax 탐색을 이 순서대로 한다.
	for (int i = 0; i<size_x; i++) {
		push_state();
		current_column = Hdrop_order[i];

		result = drop_piece(real_player, current_column);

		/* If this column is full, ignore it as a possibility. */
		if (result < 0) {
			pop_state();
			continue;
		}

		/* If this drop wins the game, take it! */
		else if (current_state->winner == real_player) {
			best_column = current_column;
			pop_state();
			break;
		}

		/* Otherwise, look ahead to see how good this move may turn out */
		/* to be (assuming the opponent makes the best moves possible). */
		else {
			next_poll = clock() + poll_interval;
			goodness = evaluate(real_player, level, -(INT_MAX), -best_worst);
			printf(" | Current column : %d, goodness : %d\n", current_column + 1, goodness);
		}

		/* If this move looks better than the ones previously considered, */
		/* remember it.                                               	*/
		if (goodness > best_worst) {
			best_worst = goodness;
			best_column = current_column;
			num_of_equal = 1;
		}

		pop_state();
	}

	move_in_progress = false;

	/* Drop the piece in the column decided upon. */

	if (best_column >= 0) {
		result = drop_piece(real_player, best_column);
		if (column != NULL)
			*column = best_column;
		if (row != NULL)
			*row = result;
		return true;
	}
	else
		return false;
}



/**
* @function c4_board
*
* @return 현재 게임 보드의 상태를 2차원 char배열로 리턴
*
* 리턴하는 2차원 배열은 column * row 순서로, 7*6 2차원 배열이다.
* 사람의 돌은 숫자 0, 컴퓨터의 돌은 숫자 1, 아무 돌도 놓여있지 않은 곳은 C4_NONE(2)으로 채워져 있다.
*/

char **
c4_board(void)
{
	assert(game_in_progress);
	return current_state->board;
}



/**
* @function c4_score_of_player
*
* @param player 현재 score를 알고 싶은 사람(0) 또는 컴퓨터(1)
* @return player의 score 값
*
* score란 남아있는 우승 가능한 연속된 돌 위치(Winning Position)의 개수와
* player가 각각의 배열을 완성하는데 얼마나 근접했는지 두 가지 요소를 고려하여 수치화한 것이다.
*/

int
c4_score_of_player(int player)
{
	assert(game_in_progress);
	return current_state->score[real_player(player)];
}




/**
* @function c4_is_winner
*
* @param player 우승여부를 알고 싶은 사람(0) 또는 컴퓨터(1)
* @return 우승했다면 true, 아니면 false
*/

bool
c4_is_winner(int player)
{
	assert(game_in_progress);
	return (current_state->winner == real_player(player));
}



/**
* @function c4_is_tie
*
* @return 게임 보드가 완성되어 무승부라면 true, 아니면 false
*/

bool
c4_is_tie(void)
{
	assert(game_in_progress);
	return (current_state->num_of_pieces == total_size &&
		current_state->winner == C4_NONE);
}




/**
* @function c4_win_coords
*
* @param x1 우승하는 연속된 4개의 돌 중 가장 아래 왼쪽 돌의 column 좌표값
* @param y1 우승하는 연속된 4개의 돌 중 가장 아래 왼쪽 돌의 row 좌표값
* @param x2 우승하는 연속된 4개의 돌 중 가장 위 오른쪽 돌의 column 좌표값
* @param y2 우승하는 연속된 4개의 돌 중 가장 위 오른쪽 돌의 row 좌표값
*
* C에서는 여러 값을 동시에 리턴하는 것이 불가능하므로,
* 상위 함수에 속해있는 변수들의 주소를 parameter로 받아 두 돌의 column과 row 값을 저장해
* 리턴 명령어를 사용하지 않고 간접적으로 값을 리턴한다.
*/

void
c4_win_coords(int *x1, int *y1, int *x2, int *y2)
{
	register int i, j, k;
	int winner, win_pos = 0;
	bool found;

	assert(game_in_progress);

	winner = current_state->winner;
	assert(winner != C4_NONE);

	while (current_state->score_array[winner][win_pos] != magic_win_number)
		win_pos++;

	/* Find the lower-left piece of the winning connection. */

	found = false;
	for (j = 0; j<size_y && !found; j++)
		for (i = 0; i<size_x && !found; i++)
			for (k = 0; map[i][j][k] != -1; k++)
				if (map[i][j][k] == win_pos) {
					*x1 = i;
					*y1 = j;
					found = true;
					break;
				}

	/* Find the upper-right piece of the winning connection. */

	found = false;
	for (j = size_y - 1; j >= 0 && !found; j--)
		for (i = size_x - 1; i >= 0 && !found; i--)
			for (k = 0; map[i][j][k] != -1; k++)
				if (map[i][j][k] == win_pos) {
					*x2 = i;
					*y2 = j;
					found = true;
					break;
				}
}



/**
* @function c4_end_game
*
* 진행되고 있는 게임을 종료하고, 게임을 실행하면서 사용되었던 모든 메모리를 비운다.
*/

void
c4_end_game(void)
{
	int i, j;

	assert(game_in_progress);
	assert(!move_in_progress);

	/* Free up the memory used by the map. */

	for (i = 0; i<size_x; i++) {
		for (j = 0; j<size_y; j++)
			free(map[i][j]);
		free(map[i]);
	}
	free(map);

	/* Free up the memory of all the states used. */

	for (i = 0; i<states_allocated; i++) {
		for (j = 0; j<size_x; j++)
			free(state_stack[i].board[j]);
		free(state_stack[i].board);
		free(state_stack[i].score_array[0]);
		free(state_stack[i].score_array[1]);
	}
	states_allocated = 0;

	/* Free up the memory used by the drop_order array. */

	free(drop_order);

	game_in_progress = false;
}



/****************************************************************************/
/****************************************************************************/
/**                                                                    	**/
/**  The following functions are local to this file and should not be  	**/
/**  called externally.                                                	**/
/**                                                                    	**/
/****************************************************************************/
/****************************************************************************/



/**
* @function num_of_win_places
*
* @param x 사용하고 있는 게임 보드의 column 개수
* @param y 사용하고 있는 게임 보드의 row 개수
* @param n 연속되게 연결해야 하는 돌의 개수
* @return 해당 게임 보드에서 우승 가능한 모든 연속된 돌의 조합(Winning Position)의 수
*/

static int
num_of_win_places(int x, int y, int n) // num_of_win_places(6, 7, 4)
{
	if (x < n && y < n)
		return 0;
	else if (x < n)
		return x * ((y - n) + 1);
	else if (y < n)
		return y * ((x - n) + 1);
	else // 항상 여기. return 69.
		return 4 * x*y - 3 * x*n - 3 * y*n + 3 * x + 3 * y - 4 * n + 2 * n*n + 2;
}



/**
* @function update_score
*
* @param player 현재 score 값을 업데이트하고 싶은 사람(0) 또는 컴퓨터(1)
* @param x 입력 받을 최소 숫자
* @param y 입력 받을 최대 숫자
*
* 현재 상태에서 player가 column x, row y 자리에 돌을 놓았을 때, 변경된 score 값을 업데이트한다.
*/

static void
update_score(int player, int x, int y)
{
	register int i;
	int win_index;
	int this_difference = 0, other_difference = 0;
	int **current_score_array = current_state->score_array;
	int other_player = other(player);

	for (i = 0; map[x][y][i] != -1; i++) {
		win_index = map[x][y][i];
		this_difference += current_score_array[player][win_index];
		other_difference += current_score_array[other_player][win_index];

		current_score_array[player][win_index] <<= 1;
		current_score_array[other_player][win_index] = 0;

		if (current_score_array[player][win_index] == magic_win_number)
			if (current_state->winner == C4_NONE)
				current_state->winner = player;
	}

	current_state->score[player] += this_difference;
	current_state->score[other_player] -= other_difference;
}



/**
* @function drop_piece
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param column 돌을 놓을 column 값
* @return 돌을 성공적으로 놓았다면, 돌을 놓은 좌표의 row 값을 리턴
*		  만약 돌을 놓지 못 했다면, -1을 리턴한다.
*
* 입력받은 player의 돌을 입력받은 column에다가 놓는 함수이다.
*/

static int
drop_piece(int player, int column)
{
	int y = 0;

	while (current_state->board[column][y] != C4_NONE && ++y < size_y)
		;

	if (y == size_y)
		return -1;

	current_state->board[column][y] = player;
	current_state->num_of_pieces++;
	update_score(player, column, y);

	return y;
}



/**
* @function push_state
*
* Game_state 안에서 돌을 놓을 수 있는 경우의 수를 테스트할 수 있도록 새로운 Game_state를 만들어 stack에 넣어주는 함수이다.
* MinMax 알고리즘 계산 시, stack에 저장된 Game_state를 push, pop하면서 돌을 놓을 최적의 좌표를 구한다.
*/

static void
push_state(void)
{
	register int i, win_places_array_size;
	Game_state *old_state, *new_state;

	win_places_array_size = win_places * sizeof(int);
	old_state = &state_stack[depth++];
	new_state = &state_stack[depth];

	if (depth == states_allocated) {

		/* Allocate space for the board */

		new_state->board = (char **)emalloc(size_x * sizeof(char *));
		for (i = 0; i<size_x; i++)
			new_state->board[i] = (char *)emalloc(size_y);

		/* Allocate space for the score array */

		new_state->score_array[0] = (int *)emalloc(win_places_array_size);
		new_state->score_array[1] = (int *)emalloc(win_places_array_size);

		states_allocated++;
	}

	/* Copy the board */

	for (i = 0; i<size_x; i++)
		memcpy(new_state->board[i], old_state->board[i], size_y);

	/* Copy the score array */

	memcpy(new_state->score_array[0], old_state->score_array[0],
		win_places_array_size);
	memcpy(new_state->score_array[1], old_state->score_array[1],
		win_places_array_size);

	new_state->score[0] = old_state->score[0];
	new_state->score[1] = old_state->score[1];
	new_state->winner = old_state->winner;
	new_state->num_of_pieces = old_state->num_of_pieces;

	current_state = new_state;
}



/**
* @function evaluate
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param level level만큼의 수를 내다봄
* @param alpha alpha-beta pruning에서 사용하기 위한 값
* @param beta alpha-beta pruning에서 사용하기 위한 값
* @return 계산 후, 현재 상태에서 발생할 수 있는 최악의 goodness 값을 리턴
*
* 현재 상태가 입력 받은 player에게 얼마나 유리한 상태인지 alpha-beta pruning을 사용하여 level만큼의 수를 내다보아 계산한다.
*/

static int
evaluate(int player, int level, int alpha, int beta)
{
	if (poll_function != NULL && next_poll <= clock()) {
		next_poll += poll_interval;
		(*poll_function)();
	}

	if (current_state->winner == player)
		return INT_MAX - depth;
	else if (current_state->winner == other(player))
		return -(INT_MAX - depth);
	else if (current_state->num_of_pieces == total_size)
		return 0; /* a tie */
	else if (level == depth)
		return goodness_of(player);
	else {
		/* Assume it is the other player's turn. */
		int best = -(INT_MAX);
		int maxab = alpha;
		int Hdrop_order[7];
		heuristicDropOrder(other(player), Hdrop_order);
		for (int i = 0; i<size_x; i++) {
			if (current_state->board[drop_order[i]][size_y - 1] != C4_NONE)
				continue; /* The column is full. */
			push_state();
			drop_piece(other(player), drop_order[i]);
			int goodness = evaluate(other(player), level, -beta, -maxab);
			if (goodness > best) {
				best = goodness;
				if (best > maxab)
					maxab = best;
			}
			pop_state();
			if (best > beta)
				break;
		}

		/* What's good for the other player is bad for this one. */
		return -best;
	}
}



/**
* @function emalloc
*
* @param size 할당할 byte 수
* @return 새로 할당한 주소의 좌표
*
* 현재 상태가 입력 받은 player에게 얼마나 유리한 상태인지 alpha-beta pruning을 사용하여 level만큼의 수를 내다보아 계산한다.
*/

static void *
emalloc(size_t size)
{
	void *ptr = malloc(size);
	if (ptr == NULL) {
		fprintf(stderr, "c4: emalloc() - Can't allocate %ld bytes.\n",
			(long)size);
		exit(1);
	}
	return ptr;
}



/**
* @function rule1_1
*
* @param player 사람(0) 또는 컴퓨터(1)
* @return Rule 1에 해당해 놓을 수 있는 돌의 좌표가 있다면 돌의 column 값을 리턴하고, 없다면 -1를 리턴
*
* Rule 1: player의 차례에 돌을 놓아 4개의 연속된 돌을 완성할 수 있다면 돌을 놓는다
*
* 강희연 작성
*/

int
rule1_1(int player) {

	int winLineArr[70]; // score 값이 8인 
	int i, j, x, y, z;
	int jx = -1;
	int iy = -1;
	bool exists = false;


	for (i = 0; i < 70; i++) {
		winLineArr[i] = -1;
	}

	r12_winning8check(player, winLineArr);

	for (i = 0; winLineArr[i] != -1; i++) {
		if (winLineArr[i] < 24) {
			x = winLineArr[i] % 4;
			y = winLineArr[i] / 4;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x + j][y] == C4_NONE) {
					jx = x + j; iy = y;
					if (iy == 0) {
						exists = true;
						break;
					}
					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}

				}
			}
		}
		else if (winLineArr[i] < 45) {
			z = winLineArr[i] - 24;
			x = z / 3;
			y = z % 3;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x][y + j] == C4_NONE) {
					jx = x; iy = y + j;
					if (iy == 0) {
						exists = true;
						break;
					}

					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}
				}
			}

		}
		else if (winLineArr[i] < 57) {
			z = winLineArr[i] - 45;
			x = z % 4;
			y = z / 4;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x + j][y + j] == C4_NONE) {
					jx = x + j; iy = y + j;
					if (iy == 0) {
						exists = true;
						break;
					}
					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}

				}
			}
		}
		else {
			z = winLineArr[i] - 57;
			x = 6 - (z % 4);
			y = z / 4;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x - j][y + j] == C4_NONE) {
					jx = x - j; iy = y + j;

					if (iy == 0) {
						exists = true;
						break;
					}
					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}
				}

			}

		}

		if (exists == true) {
			break;
		}
		else {
			jx = -1;
			iy = -1;
		}
	}
	return jx;

}



/**
* @function r12_winning8check
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param winLineArr 함수에서 찾은 Winning Position을 저장하기 위한 포인터
*
* Rule 1, 2, 6에서 사용되는 함수로,
* Winning Position 중 player에 대해 score 값이 8인 것들(Winning Position 중 player의 돌이 3개 채워진 것)을
* 포인터 winLineArr에 저장하여 상위 함수가 사용할 수 있게 한다.
*
* 강희연 작성
*/

void
r12_winning8check(int player, int* winLineArr) { // x is array of possible winning lines
	int i;
	int count = 0;

	for (i = 0; i < 69; i++) {
		if (current_state->score_array[player][i] == 8) {
			winLineArr[count] = i;
			count++;
		}
	}

}



/**
* @function rule2_1
*
* @param player 사람(0) 또는 컴퓨터(1)
* @return Rule 2에 해당해 놓을 수 있는 돌의 좌표가 있다면 돌의 column 값을 리턴하고, 없다면 -1를 리턴
*
* Rule 2: 상대방이 돌을 놓아 4개의 연속된 돌을 완성할 수 있다면 이를 막기 위해 돌을 놓는다
*
* 강희연 작성
*/



int
rule2_1(int player) {

	player = other(player);
	int winLineArr[70];
	int i, j, x, y, z;
	int jx = -1;
	int iy = -1;
	bool exists = false;


	for (i = 0; i < 70; i++) {
		winLineArr[i] = -1;
	}

	r12_winning8check(player, winLineArr);

	for (i = 0; winLineArr[i] != -1; i++) {
		if (winLineArr[i] < 24) {
			x = winLineArr[i] % 4;
			y = winLineArr[i] / 4;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x + j][y] == C4_NONE) {
					jx = x + j; iy = y;
					if (iy == 0) {
						exists = true;
						break;
					}
					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}

				}
			}
		}
		else if (winLineArr[i] < 45) {
			z = winLineArr[i] - 24;
			x = z / 3;
			y = z % 3;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x][y + j] == C4_NONE) {
					jx = x; iy = y + j;
					if (iy == 0) {
						exists = true;
						break;
					}
					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}

				}
			}

		}
		else if (winLineArr[i] < 57) {
			z = winLineArr[i] - 45;
			x = z % 4;
			y = z / 4;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x + j][y + j] == C4_NONE) {
					jx = x + j; iy = y + j;

					if (iy == 0) {
						exists = true;
						break;
					}
					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}

				}
			}
		}
		else {
			z = winLineArr[i] - 57;
			x = 6 - (z % 4);
			y = z / 4;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x - j][y + j] == C4_NONE) {
					jx = x - j; iy = y + j;

					if (iy == 0) {
						exists = true;
						break;
					}
					else if (current_state->board[jx][iy - 1] != C4_NONE) {
						exists = true;
						break;
					}

				}

			}


		}

		if (exists == true) {
			break;
		}
		else {
			jx = -1;
			iy = -1;
		}
	}
	return jx;

}



/**
* @function rule3
*
* @param player 사람(0) 또는 컴퓨터(1)
* @return Rule 3에 해당해 놓을 수 있는 돌의 좌표가 있다면 돌의 column 값을 리턴하고, 없다면 -1를 리턴
*
* Rule 3: 상대가 _ o o o _ 의 상황을 만드는 것을 저지한다
*
* 김채영 작성
*/

int
rule3(int player) {
	int sel;
	//printf("< RULE 3 >\n");
	for (int i = 0; i < 7; i++) {
		for (int j = 0; j < 6; j++) {
			if ((int)current_state->board[i][j] == 2) {
				sel = r34_horizontalCheck(other(player), i, j);
				if (sel != -1) { // horizontalCheck의 return 값은 놔야 하는 col
					return sel;
				}
				sel = r34_diagonalCheckPos(other(player), i, j);
				if (sel != -1) {
					return sel;
				}
				sel = r34_diagonalCheckNeg(other(player), i, j);
				if (sel != -1) {
					return sel;
				}
			}
		}
	}
	return -1;
}



/**
* @function rule4
*
* @param player 사람(0) 또는 컴퓨터(1)
* @return Rule 4에 해당해 놓을 수 있는 돌의 좌표가 있다면 돌의 column 값을 리턴하고, 없다면 -1를 리턴
*
* 상대의 양쪽이 모두 열려있는 3개가 완성되는 것을 막는다.
* ex)__oo_, _oo__, _o_o_
* vertical은 불가능
* diagonal(positive). a는 o나 x
*
* 김채영 작성
*/

int
rule4(int player) {
	int sel;
	//printf("< RULE 4 >\n");
	for (int i = 0; i < 7; i++) {
		for (int j = 0; j < 6; j++) {
			if ((int)current_state->board[i][j] == 2) {
				sel = r34_horizontalCheck(player, i, j);
				if (sel != -1) { // horizontalCheck의 return 값은 놔야 하는 col
					return sel;
				}
				sel = r34_diagonalCheckPos(player, i, j);
				if (sel != -1) {
					return sel;
				}
				sel = r34_diagonalCheckNeg(player, i, j);
				if (sel != -1) {
					return sel;
				}
			}
		}
	}
	return -1;
}



/**
* @function r34_diagonalCheckPos
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param col 대각선의 왼쪽 아래 시작 column 좌표
* @param row 대각선의 왼쪽 아래 시작 row 좌표
* @return 해당 대각선이 존재하지 않으면 -1, 존재하면 놓아야할 column 좌표를 리턴
*
* Rule 3, 4에 해당하는 상황이 대각선(양의 기울기)에 존재하는지 확인.
* ___oa   ____a   ___oa
* __oaa   __oaa   ___aa
* __aaa   _oaaa   _oaaa
* _aaaa   _aaaa   _aaaa
*
* 김채영 작성
*/

int
r34_diagonalCheckPos(int player, int col, int row) {
	if (col >= 3) return -1;
	//printf("Diagonal Check Pos is called\n");
	if ((int)current_state->board[col + 1][row + 1] == 2) {
		if ((current_state->board[col + 2][row + 2] == player)
			&& (current_state->board[col + 3][row + 3] == player)
			&& ((int)current_state->board[col + 4][row + 4] == 2)
			&& ((int)current_state->board[col + 1][row] != 2)
			&& ((int)current_state->board[col + 4][row + 3] != 2)) {
			if ((row > 0 && (int)current_state->board[col][row - 1] != 2) || (row == 0)) {
				//printf("Diagonal Check Pos case 1\n");
				return col + 1;
			}
		}
		//printf("here1\n");
		return -1;
	}
	else if (current_state->board[col + 1][row + 1] == player) {
		if ((current_state->board[col + 2][row + 2] == player)
			&& ((int)current_state->board[col + 3][row + 3] == 2)
			&& ((int)current_state->board[col + 4][row + 4] == 2)
			&& ((int)current_state->board[col + 3][row + 2] != 2)
			&& ((int)current_state->board[col + 4][row + 3] != 2)) {
			if ((row > 0 && (int)current_state->board[col][row - 1] != 2) || (row == 0)) {
				//printf("Diagonal Check Pos case 2\n");
				return col + 3;
			}
		}
		if ((int)(current_state->board[col + 2][row + 2] == 2)
			&& (current_state->board[col + 3][row + 3] == player)
			&& ((int)current_state->board[col + 4][row + 4] == 2)
			&& ((int)current_state->board[col + 2][row + 1] != 2)
			&& ((int)current_state->board[col + 4][row + 3] != 2)) {
			if ((row > 0 && (int)current_state->board[col][row - 1] != 2) || (row == 0)) {
				//printf("Diagonal Check Pos case 3\n");
				return col + 2;
			}
		}
		return -1;
	}
	else
		return -1;
}



/**
* @function r34_diagonalCheckNeg
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param col 대각선의 오른쪽 아래 시작 column 좌표
* @param row 대각선의 오른쪽 아래 시작 row 좌표
* @return 해당 대각선이 존재하지 않으면 -1, 존재하면 놓아야할 column 좌표를 리턴
*
* Rule 3, 4에 해당하는 상황이 대각선(음의 기울기)에 존재하는지 확인.
* _____   _____   _____
* ao___   a____   ao___
* aao__   aao__   aa___
* aaa__   aaao_   aaao_
* aaaa_   aaaa_   aaaa_   오른쪽 하단부터 북서쪽 방향으로 탐색.
*
* 김채영 작성
*/

int
r34_diagonalCheckNeg(int player, int col, int row) {
	if (col < 5) return -1;
	//printf("Diagonal Check Neg is called\n");
	if ((int)current_state->board[col - 1][row + 1] == 2) {
		if ((current_state->board[col - 2][row + 2] == player)
			&& (current_state->board[col - 3][row + 3] == player)
			&& ((int)current_state->board[col - 4][row + 4] == 2)
			&& ((int)current_state->board[col - 1][row] != 2)
			&& ((int)current_state->board[col - 4][row + 3] != 2)) {
			if ((row > 0 && (int)current_state->board[col][row - 1] != 2) || (row == 0)) {
				//printf("Diagonal Check Neg case 1\n");
				return col - 1;
			}
		}
		return -1;
	}
	else if (current_state->board[col - 1][row + 1] == player) {
		if ((current_state->board[col - 2][row + 2] == player)
			&& ((int)current_state->board[col - 3][row + 3] == 2)
			&& ((int)current_state->board[col - 4][row + 4] == 2)
			&& ((int)current_state->board[col - 3][row + 2] != 2)
			&& ((int)current_state->board[col - 4][row + 3] != 2)) {
			if ((row > 0 && (int)current_state->board[col][row - 1] != 2) || (row == 0)) {
				//printf("Diagonal Check Neg case 2\n");
				return col - 3;
			}
		}
		if ((int)(current_state->board[col - 2][row + 2] == 2)
			&& (current_state->board[col - 3][row + 3] == player)
			&& ((int)current_state->board[col - 4][row + 4] == 2)
			&& ((int)current_state->board[col - 2][row + 1] != 2)
			&& ((int)current_state->board[col - 4][row + 3] != 2)) {
			if ((row > 0 && (int)current_state->board[col][row - 1] != 2) || (row == 0)) {
				//printf("Diagonal Check Neg case 3\n");
				return col - 2;
			}
		}
		return -1;
	}
	else return -1;
}



/**
* @function r34_horizontalCheck
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param col 가로선의 왼쪽 시작 column 좌표
* @param row 가로선의 왼쪽 시작 row 좌표
* @return 해당 가로선이 존재하지 않으면 -1, 존재하면 놓아야할 column 좌표를 리턴
*
* Rule 3, 4에 해당하는 상황이 가로선에 존재하는지 확인
*
* 김채영 작성
*/

int
r34_horizontalCheck(int player, int col, int row) {
	if (col >= 3) return -1;
	//printf("Horizontal Check is called\n");
	if ((int)current_state->board[col + 1][row] == 2) { // __oo_ 이면서 빈 칸 아래에는 다 무언가로 채워져 있는 경우만 고려한다.
														//printf("check __oo_ \n");
		if ((current_state->board[col + 2][row] == player)
			&& (current_state->board[col + 3][row] == player)
			&& ((int)current_state->board[col + 4][row] == 2)
			&& ((int)current_state->board[col + 1][row - 1] != 2)
			&& ((int)current_state->board[col][row - 1] != 2)
			&& ((int)current_state->board[col + 4][row - 1] != 2)) {
			//printf("Horizontal Check case 1\n");
			return col + 1;
		}
	}
	if (current_state->board[col + 1][row] == player) { // _oo__, _o_o_
														//printf("check _oo__ and _o_o_ \n;");
		if ((current_state->board[col + 2][row] == player) // _oo__
			&& ((int)current_state->board[col + 3][row] == 2)
			&& ((int)current_state->board[col + 4][row] == 2)
			&& ((int)current_state->board[col + 3][row - 1] != 2)
			&& ((int)current_state->board[col + 4][row - 1] != 2)
			&& ((int)current_state->board[col][row - 1] != 2)) {
			//printf("Horizontal Check case 2\n");
			return col + 3;
		}
		if (((int)current_state->board[col + 2][row] == 2) // _o_o_
			&& (current_state->board[col + 3][row] == player)
			&& ((int)current_state->board[col + 4][row] == 2)
			&& ((int)current_state->board[col + 2][row - 1] != 2)
			&& ((int)current_state->board[col][row - 1] != 2)
			&& ((int)current_state->board[col + 4][row - 1] != 2)) {
			//printf("Horizontal Check case 3\n");
			return col + 2;
		}
	}
	return -1;
}



/**
* @function rule5
*
* @param player 지금 돌을 놓을 차례인 사람(0) 또는 컴퓨터(1)
* @param colArr Rule6에서 계산한 배열
* @param min colArr의 최소값
* @return 착수 성공 시 해당 칼럼을 리턴하며 적절한 위치를 찾지 못한 경우 -1을 리턴한다.
*
* Rule 5: 한 번의 착수로 돌 3개가 놓인 winning row가 2개 발생하는 상황(forced win)을 만든다.
* 상대가 완성하는 경우는 반드시 막는다.
*
* 정주혜 작성
*/

int
rule5(int player, int *colArr, int min) {   //rule5
	int win_index, i, x, y, k = 0, z;
	int **current_score_array = current_state->score_array;

	for (i = 0; i<57; i++) {
		if (current_score_array[player][i] == 4) {  //나의 forced win을 발생시킬 수 있는지 살펴본다 
			if (i<24) {      //horizontal winning row인 경우 
				y = i / 4;
				x = i % 4;
				z = x + 4;   //row의 가장 왼쪽 점의 좌표 
				while (x<z) {
					if ((current_state->board[x][y] == C4_NONE) && (current_state->board[x][y - 1] != C4_NONE)) {
						push_state();
						current_score_array = current_state->score_array;
						drop_piece(real_player(player), x);
						for (k = 0; map[x][y][k] != -1; k++) {
							win_index = map[x][y][k];
							if ((win_index>23) && (current_score_array[player][win_index] == 8)) {
								pop_state();
								if (colArr[x] == min) return x; //column 반환
								printf(" *Rule 5 was rejected by Rule 6\n");
							}
						}
						pop_state();
						current_score_array = current_state->score_array;
					}
					x++;
				}
			}

			else if (i<45) {  //vertical winning row인 경우 
				z = i - 24;
				x = z / 3;
				y = z % 3;
				push_state();
				current_score_array = current_state->score_array;
				drop_piece(real_player(player), x);
				while (map[x][y + 2][k] != -1) {  //
					win_index = map[x][y + 2][k];
					if ((win_index>44) && (current_score_array[player][win_index] == 8)) {
						pop_state();
						if (colArr[x] == min) return x; //column 반환
						printf(" *Rule 5 was rejected by Rule 6\n");
					}
					k++;
				}
				pop_state();
				current_score_array = current_state->score_array;
			}
			else if (i<57) {   //forward diagonal winning row의 경우 
				z = i - 45;
				x = z % 4;
				y = z / 4;
				z = x + 4;
				while (x<z) {
					if ((current_state->board[x][y] == C4_NONE) && (current_state->board[x][y - 1] != C4_NONE)) {
						push_state();
						current_score_array = current_state->score_array;
						drop_piece(real_player(player), x);
						for (k = 0; map[x][y][k] != -1; k++) {
							win_index = map[x][y][k];
							if ((win_index>56) && (current_score_array[player][win_index] == 8)) {
								pop_state();
								if (colArr[x] == min) return x; //column 반환
								printf(" *Rule 5 was rejected by Rule 6\n");
							}
						}
						pop_state();
						current_score_array = current_state->score_array;
					}
					x++, y++;
				}
			}
		}
		if (current_score_array[other(player)][i] == 4) {   //상대의 forced win 상황 발생을 방어한다 
			if (i<24) {  //horizontal
				y = i / 4;
				x = i % 4;
				z = x + 4;
				while (x<z) {
					if ((current_state->board[x][y] == C4_NONE) && (current_state->board[x][y - 1] != C4_NONE)) {
						push_state();
						current_score_array = current_state->score_array;
						drop_piece(other(player), x);
						for (k = 0; map[x][y][k] != -1; k++) {
							win_index = map[x][y][k];
							if ((win_index>23) && (current_score_array[other(player)][win_index] == 8)) {
								pop_state();
								if (colArr[x] == min) return x; //column 반환
								printf(" *Rule 5 was rejected by Rule 6\n");
							}
						}
						pop_state();
						current_score_array = current_state->score_array;
					}
					x++;
				}
			}
			else if (i<45) {  //
				z = i - 24;
				x = z / 3;
				y = z % 3;
				push_state();
				current_score_array = current_state->score_array;
				drop_piece(other(player), x);
				while (map[x][y + 2][k] != -1) {
					win_index = map[x][y + 2][k];
					if ((win_index>44) && (current_score_array[other(player)][win_index] == 8)) {
						pop_state();
						if (colArr[x] == min) return x; //column 반환
						printf(" *Rule 5 was rejected by Rule 6\n");
					}
					k++;
				}
				pop_state();
				current_score_array = current_state->score_array;

			}

			else if (i<57) {
				z = i - 45;
				x = z % 4;
				y = z / 4;
				z = x + 4;
				while (x<z) {
					if ((current_state->board[x][y] == C4_NONE) && (current_state->board[x][y - 1] != C4_NONE)) {
						push_state();
						current_score_array = current_state->score_array;
						drop_piece(other(player), x);
						for (k = 0; map[x][y][k] != -1; k++) {
							win_index = map[x][y][k];
							if ((win_index>56) && (current_score_array[other(player)][win_index] == 8)) {
								pop_state();
								if (colArr[x] == min) return x; //column 반환
								printf(" *Rule 5 was rejected by Rule 6\n");
							}
						}
						pop_state();
						current_score_array = current_state->score_array;
					}
					x++, y++;
				}
			}
		}
	}
	return -1;
}



/**
* @function rule6
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param colArr rule6에 해당하는 좌표의 column 값을 저장하기 위한 포인터
*
* Rule 6에 해당하는 좌표의 column들을 colArr에 저장하여 상위 함수에서 사용할 수 있도록 한다.
*
* 강희연 작성
*/

void rule6(int player, int* colArr) {
	//colArr must be int array of size 7, -1 if not applicable rule6, bigger the number higher possibility rule6

	int winLineArr[70];
	int i, j, x, y, z;
	int jx = -1;
	int iy = -1;
	int count = 0;
	bool exists = false;

	for (i = 0; i < 7; i++) {
		colArr[i] = -1;
	}


	for (i = 0; i < 70; i++) {
		winLineArr[i] = -1;
	} // initialize winLineArr for storing WinningPositions with score 8

	r12_winning8check(other(player), winLineArr);

	for (i = 0; winLineArr[i] != -1; i++) {
		if (winLineArr[i] < 24) { // horizontal WinningPositions
			x = winLineArr[i] % 4; // lower left col value of WinningPosition
			y = winLineArr[i] / 4; // lower left row value of WinningPosition
			for (j = 0; j < 4; j++) {
				if (current_state->board[x + j][y] == C4_NONE) {
					jx = x + j; iy = y; //empty coordinate
					if (iy - 1 == 0 && current_state->board[jx][iy - 1] == C4_NONE) {
						colArr[jx]++;
					}
					else if (iy - 1 > 0 && current_state->board[jx][iy - 1] == C4_NONE && current_state->board[jx][iy - 2] != C4_NONE) {
						colArr[jx]++;
					}
				}
			}
		}
		else if (winLineArr[i] < 45) {
			//not applicable in rule6 - 세로로 만들 때, 위로 쌓이기만 하기 때문에 불가능함
		}
		else if (winLineArr[i] < 57) { //posdiagonal
			z = winLineArr[i] - 45;
			x = z % 4; // lower left
			y = z / 4; // lower left
			for (j = 0; j < 4; j++) {
				if (current_state->board[x + j][y + j] == C4_NONE) {
					jx = x + j; iy = y + j; // empty coordinate
					if (iy - 1 == 0 && current_state->board[jx][iy - 1] == C4_NONE) {
						// not applicable in this case - will be caught by rule 2 but just in case
						colArr[jx]++;
					}
					else if (iy - 1 > 0 && current_state->board[jx][iy - 1] == C4_NONE && current_state->board[jx][iy - 2] != C4_NONE) {
						colArr[jx]++;
					}
				}
			}
		}
		else {
			z = winLineArr[i] - 57;
			x = 6 - (z % 4);
			y = z / 4;
			for (j = 0; j < 4; j++) {
				if (current_state->board[x - j][y + j] == C4_NONE) {
					jx = x - j; iy = y + j;
					if (iy - 1 == 0 && current_state->board[jx][iy - 1] == C4_NONE) {
						// not applicable in this case - will be caught by rule 2 but just in case
						colArr[jx]++;
					}
					else if (iy - 1 > 0 && current_state->board[jx][iy - 1] == C4_NONE && current_state->board[jx][iy - 2] != C4_NONE) {
						colArr[jx]++;
					}
				}
			}
		}
	}

}



/**
* @function defaultRule
*
* @param player 사람(0) 또는 컴퓨터(1)
* @param column 돌을 놓을 column 값을 저장하기 위한 포인터
* @param colArr Rule6에서 계산한 배열
* @param min colArr의 최소값
* @return 돌을 놓을 좌표의 row 값을 리턴한다
*
* 앞선 룰들에 걸리지 않았을 때 실행되는 함수이다.
* 상대방의 직전 수 위에 놓는 것을 기본으로, 상대방의 직전 수가 맨 위 row였다면
* 나머지 column들 중에서 아직 놓을 자리가 남은 column 중 가장 높이 쌓여 있는 column 위에 돌을 놓는다.
* Column 높이가 같은 여러 개의 column이 있다면 drop_order 배열의 순서를 따른다.
*
* 정주혜 작성
*/

int defaultRule(int player, int *column, int* colArr, int min) {

	int i, x = 0, largest = -1, col, y = 0;

	if (current_state->num_of_pieces == 0) {                 //첫번째 플레이어일 경우 첫수에는 랜덤으로 2 or 4 column 선택
		if ((rand() % 2) == 0) {
			if (column != NULL) *column = 2;
			return drop_piece(real_player(player), 2);
		}
		else {
			if (column != NULL) *column = 4;
			return drop_piece(real_player(player), 4);
		}
	}

	while (current_state->board[*column][y] != C4_NONE && ++y < size_y)
		;

	if (y != size_y) {              //상대방의 직전 수 위에 놓는다
		if (colArr[*column] == min) return drop_piece(real_player(player), *column);
	}
	for (i = 0; i<7; i++) {     //상대가 column의 마지막 칸에 수를 놓은 경우 돌이 가장 많이 놓인 column 위에 둔다
		y = 0;
		col = drop_order[i];

		if (colArr[i] != min) continue;

		while (current_state->board[col][y] != C4_NONE && ++y < size_y)   //col의 가장 윗자리 row 찾는다 
			;
		if (y == size_y) continue;

		if (y > largest) {
			largest = y;
			x = col;
		}
	}

	if (y != size_y) {     //game is not tie
		*column = x;
		return drop_piece(real_player(player), x);
	}
	else return -1;
}



/**
* @func heuristicDropOrder
*
* @param player 지금 돌을 놓을 차례인 사람(0) 또는 컴퓨터(1)
* @param dropOrder Heuristic 진행 시, 탐색할 column의 순서를 저장하기 위한 포인터
*
* 모든 column에 대해 돌을 놓을 수 있는 (column, row) 좌표를 구한 후,
* 각 좌표에 대해 지나가는Winning Position의 score의 sum을 구한 후,
* 이를 바탕으로 Heuristic 진행 시, 탐색할 column의 순서를 정해 dropOrder에 저장해 상위 함수에 리턴한다.
*
* 강희연 작성
*/

void heuristicDropOrder(int player, int* dropOrder) {
	int i, j, y, r, k;
	int rowArr[7];
	int scoreArr[7];

	for (i = 0; i < 7; i++) {              // initialize scoreArr
		scoreArr[i] = 0;
	}

	for (i = 0; i < 7; i++) {              //store value of possible col, row coordinates in rowArr
		y = 0;

		while (current_state->board[i][y] != C4_NONE && ++y < size_y)   //col의 가장 윗자리 row 찾는다 
			;

		rowArr[i] = y;
	}

	for (i = 0; i < 7; i++) { // 각 column에 대해
		j = 0;
		r = rowArr[i];
		if (r == 6) continue;
		while (map[i][r][j] != -1) { // winning Line에 대해
			k = map[i][r][j];
			scoreArr[i] += current_state->score_array[player][k]; //해당 winning line의 score 더하기, scoreArr에 각 col의 sum of score있음
			j++;
		}
	}

	int maxidx, max, s;
	int count = 0;

	while (count < 7) {
		maxidx = drop_order[0];              //drop_order={3 4 2 5 1 6 0}, 점수가 같을 경우 중앙에서 가까운 칼럼을 우선한다
		max = scoreArr[drop_order[0]];
		for (s = 1; s < 7; s++) {
			if (max < scoreArr[drop_order[s]]) {
				max = scoreArr[drop_order[s]];
				maxidx = drop_order[s];
			}
		}
		scoreArr[maxidx] = -1;
		dropOrder[count++] = maxidx;   //점수가 가장 높은 칼럼 순으로 정렬
	}
}