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
* Alpha-beta cutoff �˰��� ����ؼ� �ð� ����.
* c4_�� �����ϴ� public function���� c4.h�� ����.
* Player�� value�� �����ε� ¦���� player 0, Ȧ���� player 1��.
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
* ���Ǹ� ���� ��ũ��
*/

#define other(x)    	((x) ^ 1) // 
#define real_player(x)  ((x) & 1)

#define pop_state() (current_state = &state_stack[--depth])



/**
* ���� ���¿� ���� Ư�� player�� "goodness"�� �ڽ��� score����
* ������ score�� �� ���̴�. goodness�� ���� ������, �ش� player��
* �ڽ��� ���溸�� �� ���� ��Ȳ�� �ִٴ� ���� ���Ѵ�.
*/

#define goodness_of(player) (current_state->score[player] - current_state->score[other(player)])



/**
* Game_state ����ü�� ������ ���¸� ǥ��.
*/

typedef struct {

	char **board;       	// ���� ���带 ǥ���ϱ� ���� ������ �迭. ��, ���� 0���� ����. 
							// C4_NONE���� ä������ �� ĭ, 0�̸� ���, 1�̸� ��ǻ��.

	int *(score_array[2]);	// �� Winning Positions�� ���� player 0�� 1�� score ���� ������ �迭
							// Player 0, 1�� �� ����ü�� ǥ���ϱ� ���� 2���� �迭�� ����Ͽ���.

	int score[2];       	// score_array���� �� �� �ִ� �� player�� score ��
							// player x�� score ���� score_array[x]�� ��� ���� ���̴�.

	short int winner;   	// ������ �¸��� - 0, 1, �Ǵ� ���ºζ�� C4_NONE
							// score_array������ �� �� ������, ȿ������ ���� �ٸ� ������ ���.

	int num_of_pieces;  	// ���� ���� ���� ���� ������ ���� �� ����

} Game_state;



/**
* Static global variables
*/

static int size_x, size_y, total_size;
static int num_to_connect;
static int win_places;

static int ***map;  // map[x][y] win place �ε������ �̷���� �迭, -1�� ��������

static int magic_win_number;
static bool game_in_progress = false, move_in_progress = false;
static bool seed_chosen = false;
static void(*poll_function)(void) = NULL;
static clock_t poll_interval, next_poll;
static Game_state state_stack[C4_MAX_LEVEL + 1]; // ���� 21�� �迭
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
* @param (*poll_func)(void) �����ų �Լ�
* @param interval ����� �Լ��� ����
*
* interval �������� ù ��° argument�� �Լ��� �����Ѵ�.
* �츮�� c4_poll(print_dot, CLOCKS_PER_SEC / 2)�� ������� �� �Լ��� ����ߴµ�,
* �̰��� 0.5�� �������� print_dot()�� �����϶�� ���̴�.
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
* ���ο� ������ �����ϱ� ��,
* ���� ���� ũ��(6*7)�� ����ϱ� ���� �����ؾ� �ϴ� ���ӵ� �� ��(4)�� �����Ѵ�.
* ����, ��� ������ ���ӵ� �� ��ġ�� ��� ����� ���� �迭�� �����. ��
*  �Լ��� ���ο� ������ �����ϱ� ���ؼ� �ʼ������� �ҷ��� �ϸ�,
* �� ������ ������ �� �ٽ� �θ� �� ����.
*/

void
c4_new_game() // ���� ����!
{
	register int i, j, k, x;
	int win_index, column;
	int *win_indices;

	assert(!game_in_progress); // ��ȣ ���� true�� pass, �����̸� ���� �޽��� ���

	size_x = WIDTH;
	size_y = HEIGHT;
	total_size = WIDTH * HEIGHT;
	num_to_connect = NUM_TO_CONNECT;
	magic_win_number = 1 << num_to_connect; // magic_win_number = 16
	win_places = num_of_win_places(size_x, size_y, num_to_connect); // win_places = 69. �̱� �� �ִ� ������ ��� ��.

	if (!seed_chosen) { // ���� score�� �� ������ random����.
		srand((unsigned int)time((time_t *)0));
		seed_chosen = true;
	}

	/* ���� �����ϱ� */

	depth = 0;
	current_state = &state_stack[0]; // initial state

	current_state->board = (char **)emalloc(size_x * sizeof(char *)); // ������ �迭 board�� ���� ����(6x7)�� �����ϰ� C4_NONE(=2)���� ä��.
	for (i = 0; i<size_x; i++) {
		current_state->board[i] = (char *)emalloc(size_y);
		for (j = 0; j<size_y; j++)
			current_state->board[i][j] = C4_NONE;
	}

	/* score_array �����ϱ� */

	current_state->score_array[0] = (int *)emalloc(win_places * sizeof(int)); // 69���� ��� win_places�� ���� score�� ����� ��.
	current_state->score_array[1] = (int *)emalloc(win_places * sizeof(int));
	for (i = 0; i<win_places; i++) { // �ϴ��� ��� 1.
		current_state->score_array[0][i] = 1;
		current_state->score_array[1][i] = 1;
	}

	current_state->score[0] = current_state->score[1] = win_places; // Player 0�� 1�� �ʱ� ���� = 69.
	current_state->winner = C4_NONE;  // winner�� ���� ����.
	current_state->num_of_pieces = 0; // initial state�̹Ƿ� ���� ���� 0��.

	states_allocated = 1;

	/* map �����ϱ� */

	map = (int ***)emalloc(size_x * sizeof(int **)); // map�� 3���� �迭. 6x7x17�� int�� �� ���� �Ҵ�. map[all][all][0] = -1���� �ʱ�ȭ.
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
* @param player ���� ���� ���� ������ ���(0) �Ǵ� ��ǻ��(1)
* @param column ���� ���� ���� ����
* @param row ���� ���� ���� ����
* @return ��ǥ�� ���� �� ���� �ڸ���� false�� �����ϰ�,
*         ���������� ���Ҵٸ�, true�� ����
*
* parameter���� �Էµ� ����� (��� �Ǵ� ���)�� �ش��ϴ� ����
* �Էµ� (row, column) ��ǥ�� �°� ���´�
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
* @param player ���� ���� ���� ������ ���(0) �Ǵ� ��ǻ��(1)
* @param column ���� ���� ���� ��ǥ���� �����ϱ� ���� ���Ǵ� ������
* @param row ���� ���� ���� ��ǥ���� �����ϱ� ���� ���Ǵ� ������
* @return ���� ���� ���尡 �� ���� ���� �ڸ��� ���ٸ� false�� ����,
*         ���������� ���Ҵٸ�, true�� ����
*
* ��ǻ�Ͱ� Heuristic�̳� Rule �߿��� ������ �������� ���� ���� ���ΰ� ������� ��,
* Heuristic �� ���õǾ��ٸ� ����Ǵ� �Լ��̴�.
* parameter���� �Էµ� �����(player)�� ���� ��ǻ�Ͱ� Ž��Ʈ���� level ��ŭ Ž���Ͽ� ���� ���⿡ ������ ��ǥ�� ���ϰ�,
* �� �ڸ��� ���� ���´�. ������ column, row�� ���� ���� ��ǥ���� �����Ѵ�.
*
* ��� ������ �Բ� �ۼ��� �ڵ��, ���� �ۼ��� Rule���� �� �Լ����� �θ� �� �ֵ��� �ۼ��Ͽ���.
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
* @param player ���� ���� ���� ������ ���(0) �Ǵ� ��ǻ��(1)
* @param level Ž�� Ʈ������ Ž���� ������ ����
* @param column ���� ���� ���� ��ǥ���� �����ϱ� ���� ���Ǵ� ������
* @param row ���� ���� ���� ��ǥ���� �����ϱ� ���� ���Ǵ� ������
* @return ���� ���� ���尡 �� ���� ���� �ڸ��� ���ٸ� false�� ����,
*         ���������� ���Ҵٸ�, true�� ����
*
* ��ǻ�Ͱ� Heuristic�̳� Rule �߿��� ������ �������� ���� ���� ���ΰ� ������� ��,
* Heuristic �� ���õǾ��ٸ� ����Ǵ� �Լ��̴�.
* parameter���� �Էµ� �����(player)�� ���� ��ǻ�Ͱ� Ž��Ʈ���� level ��ŭ Ž���Ͽ� ���� ���⿡ ������ ��ǥ�� ���ϰ�,
* �� �ڸ��� ���� ���´�. ������ column, row�� ���� ���� ��ǥ���� �����Ѵ�.
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
	heuristicDropOrder(real_player, Hdrop_order);    //Į�� �� ������ ����� ���� ���� Į�� ������ ���Ŀ� minmax Ž���� �� ������� �Ѵ�.
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
* @return ���� ���� ������ ���¸� 2���� char�迭�� ����
*
* �����ϴ� 2���� �迭�� column * row ������, 7*6 2���� �迭�̴�.
* ����� ���� ���� 0, ��ǻ���� ���� ���� 1, �ƹ� ���� �������� ���� ���� C4_NONE(2)���� ä���� �ִ�.
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
* @param player ���� score�� �˰� ���� ���(0) �Ǵ� ��ǻ��(1)
* @return player�� score ��
*
* score�� �����ִ� ��� ������ ���ӵ� �� ��ġ(Winning Position)�� ������
* player�� ������ �迭�� �ϼ��ϴµ� �󸶳� �����ߴ��� �� ���� ��Ҹ� ����Ͽ� ��ġȭ�� ���̴�.
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
* @param player ��¿��θ� �˰� ���� ���(0) �Ǵ� ��ǻ��(1)
* @return ����ߴٸ� true, �ƴϸ� false
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
* @return ���� ���尡 �ϼ��Ǿ� ���ºζ�� true, �ƴϸ� false
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
* @param x1 ����ϴ� ���ӵ� 4���� �� �� ���� �Ʒ� ���� ���� column ��ǥ��
* @param y1 ����ϴ� ���ӵ� 4���� �� �� ���� �Ʒ� ���� ���� row ��ǥ��
* @param x2 ����ϴ� ���ӵ� 4���� �� �� ���� �� ������ ���� column ��ǥ��
* @param y2 ����ϴ� ���ӵ� 4���� �� �� ���� �� ������ ���� row ��ǥ��
*
* C������ ���� ���� ���ÿ� �����ϴ� ���� �Ұ����ϹǷ�,
* ���� �Լ��� �����ִ� �������� �ּҸ� parameter�� �޾� �� ���� column�� row ���� ������
* ���� ��ɾ ������� �ʰ� ���������� ���� �����Ѵ�.
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
* ����ǰ� �ִ� ������ �����ϰ�, ������ �����ϸ鼭 ���Ǿ��� ��� �޸𸮸� ����.
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
* @param x ����ϰ� �ִ� ���� ������ column ����
* @param y ����ϰ� �ִ� ���� ������ row ����
* @param n ���ӵǰ� �����ؾ� �ϴ� ���� ����
* @return �ش� ���� ���忡�� ��� ������ ��� ���ӵ� ���� ����(Winning Position)�� ��
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
	else // �׻� ����. return 69.
		return 4 * x*y - 3 * x*n - 3 * y*n + 3 * x + 3 * y - 4 * n + 2 * n*n + 2;
}



/**
* @function update_score
*
* @param player ���� score ���� ������Ʈ�ϰ� ���� ���(0) �Ǵ� ��ǻ��(1)
* @param x �Է� ���� �ּ� ����
* @param y �Է� ���� �ִ� ����
*
* ���� ���¿��� player�� column x, row y �ڸ��� ���� ������ ��, ����� score ���� ������Ʈ�Ѵ�.
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param column ���� ���� column ��
* @return ���� ���������� ���Ҵٸ�, ���� ���� ��ǥ�� row ���� ����
*		  ���� ���� ���� �� �ߴٸ�, -1�� �����Ѵ�.
*
* �Է¹��� player�� ���� �Է¹��� column���ٰ� ���� �Լ��̴�.
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
* Game_state �ȿ��� ���� ���� �� �ִ� ����� ���� �׽�Ʈ�� �� �ֵ��� ���ο� Game_state�� ����� stack�� �־��ִ� �Լ��̴�.
* MinMax �˰��� ��� ��, stack�� ����� Game_state�� push, pop�ϸ鼭 ���� ���� ������ ��ǥ�� ���Ѵ�.
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param level level��ŭ�� ���� ���ٺ�
* @param alpha alpha-beta pruning���� ����ϱ� ���� ��
* @param beta alpha-beta pruning���� ����ϱ� ���� ��
* @return ��� ��, ���� ���¿��� �߻��� �� �ִ� �־��� goodness ���� ����
*
* ���� ���°� �Է� ���� player���� �󸶳� ������ �������� alpha-beta pruning�� ����Ͽ� level��ŭ�� ���� ���ٺ��� ����Ѵ�.
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
* @param size �Ҵ��� byte ��
* @return ���� �Ҵ��� �ּ��� ��ǥ
*
* ���� ���°� �Է� ���� player���� �󸶳� ������ �������� alpha-beta pruning�� ����Ͽ� level��ŭ�� ���� ���ٺ��� ����Ѵ�.
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @return Rule 1�� �ش��� ���� �� �ִ� ���� ��ǥ�� �ִٸ� ���� column ���� �����ϰ�, ���ٸ� -1�� ����
*
* Rule 1: player�� ���ʿ� ���� ���� 4���� ���ӵ� ���� �ϼ��� �� �ִٸ� ���� ���´�
*
* ���� �ۼ�
*/

int
rule1_1(int player) {

	int winLineArr[70]; // score ���� 8�� 
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param winLineArr �Լ����� ã�� Winning Position�� �����ϱ� ���� ������
*
* Rule 1, 2, 6���� ���Ǵ� �Լ���,
* Winning Position �� player�� ���� score ���� 8�� �͵�(Winning Position �� player�� ���� 3�� ä���� ��)��
* ������ winLineArr�� �����Ͽ� ���� �Լ��� ����� �� �ְ� �Ѵ�.
*
* ���� �ۼ�
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @return Rule 2�� �ش��� ���� �� �ִ� ���� ��ǥ�� �ִٸ� ���� column ���� �����ϰ�, ���ٸ� -1�� ����
*
* Rule 2: ������ ���� ���� 4���� ���ӵ� ���� �ϼ��� �� �ִٸ� �̸� ���� ���� ���� ���´�
*
* ���� �ۼ�
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @return Rule 3�� �ش��� ���� �� �ִ� ���� ��ǥ�� �ִٸ� ���� column ���� �����ϰ�, ���ٸ� -1�� ����
*
* Rule 3: ��밡 _ o o o _ �� ��Ȳ�� ����� ���� �����Ѵ�
*
* ��ä�� �ۼ�
*/

int
rule3(int player) {
	int sel;
	//printf("< RULE 3 >\n");
	for (int i = 0; i < 7; i++) {
		for (int j = 0; j < 6; j++) {
			if ((int)current_state->board[i][j] == 2) {
				sel = r34_horizontalCheck(other(player), i, j);
				if (sel != -1) { // horizontalCheck�� return ���� ���� �ϴ� col
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @return Rule 4�� �ش��� ���� �� �ִ� ���� ��ǥ�� �ִٸ� ���� column ���� �����ϰ�, ���ٸ� -1�� ����
*
* ����� ������ ��� �����ִ� 3���� �ϼ��Ǵ� ���� ���´�.
* ex)__oo_, _oo__, _o_o_
* vertical�� �Ұ���
* diagonal(positive). a�� o�� x
*
* ��ä�� �ۼ�
*/

int
rule4(int player) {
	int sel;
	//printf("< RULE 4 >\n");
	for (int i = 0; i < 7; i++) {
		for (int j = 0; j < 6; j++) {
			if ((int)current_state->board[i][j] == 2) {
				sel = r34_horizontalCheck(player, i, j);
				if (sel != -1) { // horizontalCheck�� return ���� ���� �ϴ� col
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param col �밢���� ���� �Ʒ� ���� column ��ǥ
* @param row �밢���� ���� �Ʒ� ���� row ��ǥ
* @return �ش� �밢���� �������� ������ -1, �����ϸ� ���ƾ��� column ��ǥ�� ����
*
* Rule 3, 4�� �ش��ϴ� ��Ȳ�� �밢��(���� ����)�� �����ϴ��� Ȯ��.
* ___oa   ____a   ___oa
* __oaa   __oaa   ___aa
* __aaa   _oaaa   _oaaa
* _aaaa   _aaaa   _aaaa
*
* ��ä�� �ۼ�
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param col �밢���� ������ �Ʒ� ���� column ��ǥ
* @param row �밢���� ������ �Ʒ� ���� row ��ǥ
* @return �ش� �밢���� �������� ������ -1, �����ϸ� ���ƾ��� column ��ǥ�� ����
*
* Rule 3, 4�� �ش��ϴ� ��Ȳ�� �밢��(���� ����)�� �����ϴ��� Ȯ��.
* _____   _____   _____
* ao___   a____   ao___
* aao__   aao__   aa___
* aaa__   aaao_   aaao_
* aaaa_   aaaa_   aaaa_   ������ �ϴܺ��� �ϼ��� �������� Ž��.
*
* ��ä�� �ۼ�
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param col ���μ��� ���� ���� column ��ǥ
* @param row ���μ��� ���� ���� row ��ǥ
* @return �ش� ���μ��� �������� ������ -1, �����ϸ� ���ƾ��� column ��ǥ�� ����
*
* Rule 3, 4�� �ش��ϴ� ��Ȳ�� ���μ��� �����ϴ��� Ȯ��
*
* ��ä�� �ۼ�
*/

int
r34_horizontalCheck(int player, int col, int row) {
	if (col >= 3) return -1;
	//printf("Horizontal Check is called\n");
	if ((int)current_state->board[col + 1][row] == 2) { // __oo_ �̸鼭 �� ĭ �Ʒ����� �� ���𰡷� ä���� �ִ� ��츸 ����Ѵ�.
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
* @param player ���� ���� ���� ������ ���(0) �Ǵ� ��ǻ��(1)
* @param colArr Rule6���� ����� �迭
* @param min colArr�� �ּҰ�
* @return ���� ���� �� �ش� Į���� �����ϸ� ������ ��ġ�� ã�� ���� ��� -1�� �����Ѵ�.
*
* Rule 5: �� ���� ������ �� 3���� ���� winning row�� 2�� �߻��ϴ� ��Ȳ(forced win)�� �����.
* ��밡 �ϼ��ϴ� ���� �ݵ�� ���´�.
*
* ������ �ۼ�
*/

int
rule5(int player, int *colArr, int min) {   //rule5
	int win_index, i, x, y, k = 0, z;
	int **current_score_array = current_state->score_array;

	for (i = 0; i<57; i++) {
		if (current_score_array[player][i] == 4) {  //���� forced win�� �߻���ų �� �ִ��� ���캻�� 
			if (i<24) {      //horizontal winning row�� ��� 
				y = i / 4;
				x = i % 4;
				z = x + 4;   //row�� ���� ���� ���� ��ǥ 
				while (x<z) {
					if ((current_state->board[x][y] == C4_NONE) && (current_state->board[x][y - 1] != C4_NONE)) {
						push_state();
						current_score_array = current_state->score_array;
						drop_piece(real_player(player), x);
						for (k = 0; map[x][y][k] != -1; k++) {
							win_index = map[x][y][k];
							if ((win_index>23) && (current_score_array[player][win_index] == 8)) {
								pop_state();
								if (colArr[x] == min) return x; //column ��ȯ
								printf(" *Rule 5 was rejected by Rule 6\n");
							}
						}
						pop_state();
						current_score_array = current_state->score_array;
					}
					x++;
				}
			}

			else if (i<45) {  //vertical winning row�� ��� 
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
						if (colArr[x] == min) return x; //column ��ȯ
						printf(" *Rule 5 was rejected by Rule 6\n");
					}
					k++;
				}
				pop_state();
				current_score_array = current_state->score_array;
			}
			else if (i<57) {   //forward diagonal winning row�� ��� 
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
								if (colArr[x] == min) return x; //column ��ȯ
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
		if (current_score_array[other(player)][i] == 4) {   //����� forced win ��Ȳ �߻��� ����Ѵ� 
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
								if (colArr[x] == min) return x; //column ��ȯ
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
						if (colArr[x] == min) return x; //column ��ȯ
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
								if (colArr[x] == min) return x; //column ��ȯ
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param colArr rule6�� �ش��ϴ� ��ǥ�� column ���� �����ϱ� ���� ������
*
* Rule 6�� �ش��ϴ� ��ǥ�� column���� colArr�� �����Ͽ� ���� �Լ����� ����� �� �ֵ��� �Ѵ�.
*
* ���� �ۼ�
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
			//not applicable in rule6 - ���η� ���� ��, ���� ���̱⸸ �ϱ� ������ �Ұ�����
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
* @param player ���(0) �Ǵ� ��ǻ��(1)
* @param column ���� ���� column ���� �����ϱ� ���� ������
* @param colArr Rule6���� ����� �迭
* @param min colArr�� �ּҰ�
* @return ���� ���� ��ǥ�� row ���� �����Ѵ�
*
* �ռ� ��鿡 �ɸ��� �ʾ��� �� ����Ǵ� �Լ��̴�.
* ������ ���� �� ���� ���� ���� �⺻����, ������ ���� ���� �� �� row���ٸ�
* ������ column�� �߿��� ���� ���� �ڸ��� ���� column �� ���� ���� �׿� �ִ� column ���� ���� ���´�.
* Column ���̰� ���� ���� ���� column�� �ִٸ� drop_order �迭�� ������ ������.
*
* ������ �ۼ�
*/

int defaultRule(int player, int *column, int* colArr, int min) {

	int i, x = 0, largest = -1, col, y = 0;

	if (current_state->num_of_pieces == 0) {                 //ù��° �÷��̾��� ��� ù������ �������� 2 or 4 column ����
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

	if (y != size_y) {              //������ ���� �� ���� ���´�
		if (colArr[*column] == min) return drop_piece(real_player(player), *column);
	}
	for (i = 0; i<7; i++) {     //��밡 column�� ������ ĭ�� ���� ���� ��� ���� ���� ���� ���� column ���� �д�
		y = 0;
		col = drop_order[i];

		if (colArr[i] != min) continue;

		while (current_state->board[col][y] != C4_NONE && ++y < size_y)   //col�� ���� ���ڸ� row ã�´� 
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
* @param player ���� ���� ���� ������ ���(0) �Ǵ� ��ǻ��(1)
* @param dropOrder Heuristic ���� ��, Ž���� column�� ������ �����ϱ� ���� ������
*
* ��� column�� ���� ���� ���� �� �ִ� (column, row) ��ǥ�� ���� ��,
* �� ��ǥ�� ���� ��������Winning Position�� score�� sum�� ���� ��,
* �̸� �������� Heuristic ���� ��, Ž���� column�� ������ ���� dropOrder�� ������ ���� �Լ��� �����Ѵ�.
*
* ���� �ۼ�
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

		while (current_state->board[i][y] != C4_NONE && ++y < size_y)   //col�� ���� ���ڸ� row ã�´� 
			;

		rowArr[i] = y;
	}

	for (i = 0; i < 7; i++) { // �� column�� ����
		j = 0;
		r = rowArr[i];
		if (r == 6) continue;
		while (map[i][r][j] != -1) { // winning Line�� ����
			k = map[i][r][j];
			scoreArr[i] += current_state->score_array[player][k]; //�ش� winning line�� score ���ϱ�, scoreArr�� �� col�� sum of score����
			j++;
		}
	}

	int maxidx, max, s;
	int count = 0;

	while (count < 7) {
		maxidx = drop_order[0];              //drop_order={3 4 2 5 1 6 0}, ������ ���� ��� �߾ӿ��� ����� Į���� �켱�Ѵ�
		max = scoreArr[drop_order[0]];
		for (s = 1; s < 7; s++) {
			if (max < scoreArr[drop_order[s]]) {
				max = scoreArr[drop_order[s]];
				maxidx = drop_order[s];
			}
		}
		scoreArr[maxidx] = -1;
		dropOrder[count++] = maxidx;   //������ ���� ���� Į�� ������ ����
	}
}