

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

**                          Sample Implementation!                        **

**                                                                        **

**  This code is poorly written and contains no internal documentation.   **

**  Its sole purpose is to quickly demonstrate an actual implementation   **

**  of the functions contained in the file "c4.c".  It's a fully working  **

**  game which should work on any type of system, so give it a shot!      **

**                                                                        **

**  The computer is pretty brain-dead at level 3 or less, but at level 4  **

**  and up it provides quite a challenge!                                 **

**                                                                        **

****************************************************************************

**  $Id: game.c,v 3.11 2009/11/03 14:42:16 pomakis Exp pomakis $

***************************************************************************/

#define _CRT_SECURE_NO_WARNINGS


#include <stdio.h>

#include <stdlib.h>

#include <ctype.h>

#include "c4.h"


enum { HUMAN = 0, COMPUTER = 1 };


static int get_num(char *prompt, int lower, int upper, int default_val);

static void print_board(void);

static void print_dot(void);


static char piece[2] = { 'X', 'O' };


int

main()

{

	int player[2], level[2], turn = 0, num_of_players, move;

	int x1, y1, x2, y2, r, c;

	char buffer[80];


	printf("\n****  Welcome to the game of Connect!  ****\n\n");

	printf("By Keith Pomakis (pomakis@pobox.com)\n");

	printf("April, 1998\n\n");


	num_of_players = 1; //get_num("Number of human players (0, 1 or 2)", 0, 2, 1);


	player[0] = HUMAN;

	player[1] = COMPUTER;

	level[1] = 13; //  get_num("Skill level of computer", 1, C4_MAX_LEVEL, 5);

	buffer[0] = '\0';

	do {

		printf("Would you like to go first [y]? ");

		if (fgets(buffer, sizeof(buffer), stdin) == NULL) {

			printf("\nGoodbye!\n");

			exit(0);

		}

		buffer[0] = tolower(buffer[0]);

	} while (buffer[0] != 'y' && buffer[0] != 'n' && buffer[0] != '\n');

	turn = (buffer[0] == 'n') ? 1 : 0;


	c4_new_game(); // 시작!

	c4_poll(print_dot, CLOCKS_PER_SEC / 2);


	do {

		print_board();

		if (player[turn] == HUMAN) {

			do {

				printf(" * Drop position : ");

				scanf("%d, %d", &r, &c);

				move = c - 1;

			} while (!(c4_make_move(turn, move, r - 1)));

		}


		else {

			fflush(stdout);

			c4_auto_move(turn, level[turn], &move, &x1);

			printf("\n * I dropped my piece on (%d, %d).\n", x1 + 1, move + 1);

		}


		turn = !turn;


	} while (!c4_is_winner(0) && !c4_is_winner(1) && !c4_is_tie());


	print_board();


	if (c4_is_winner(0)) {

		if (num_of_players == 1)

			printf("You won!");

		else

			printf("Player %c won!", piece[0]);

		c4_win_coords(&x1, &y1, &x2, &y2);

		printf("  (%d, %d) to (%d, %d)\n\n", y1 + 1, x1 + 1, y2 + 1, x2 + 1);

	}

	else if (c4_is_winner(1)) {

		if (num_of_players == 1)

			printf("I won!");

		else

			printf("Player %c won!", piece[1]);

		c4_win_coords(&x1, &y1, &x2, &y2);

		printf("  (%d, %d) to (%d, %d)\n\n", y1 + 1, x1 + 1, y2 + 1, x2 + 1);

	}

	else {

		printf("There was a tie!\n\n");

	}


	c4_end_game();

	return 0;

}


/**

* @function get_num

*

* @param prompt 화면에 띄울 문자열

* @param lower 입력 받을 최소 숫자

* @param upper 입력 받을 최대 숫자

* @param default_value 기본값

* @return 입력값이 없다면 default_value, 최솟값과 최댓값 범위에 맞는 입력값이 있다면 해당 입력값

*

* 숫자를 입력 받기 위한 함수로, prompt의 문자열과 함께 기본값(default_value)를 제시해 보여준다.

* 입력 받을 숫자의 최솟값과 최댓값이 정해져 있어서 범위 밖의 숫자를 입력하면 다시 입력하도록 한다.

*/


static int

get_num(char *prompt, int lower, int upper, int default_value)

{

	int number = -1;

	int result;

	static char numbuf[40];


	do {

		if (default_value != -1)

			printf("%s [%d]? ", prompt, default_value);

		else

			printf("%s? ", prompt);


		if (fgets(numbuf, sizeof(numbuf), stdin) == NULL || numbuf[0] == 'q') {

			printf("\nGoodbye!\n");

			exit(0);

		}

		result = sscanf(numbuf, "%d", &number);

	} while (result == 0 || (result != EOF && (number<lower || number>upper)));


	return ((result == EOF) ? default_value : number);

}


/**

* @function print_board

*

* 현재 상태의 게임 보드(current_state->board)를 출력한다.

*/


static void

print_board()

{

	int x, y;

	char **board, spacing[2], dashing[2];


	board = c4_board();


	spacing[1] = dashing[1] = '\0';

	spacing[0] = ' ';

	dashing[0] = '-';


	printf("\n\n");

	for (y = HEIGHT - 1; y >= 0; y--) {


		printf("|");

		for (x = 0; x<WIDTH; x++) {

			if (board[x][y] == C4_NONE)

				printf("%s %s|", spacing, spacing);

			else

				printf("%s%c%s|", spacing, piece[(int)board[x][y]], spacing);

		}

		printf("\n");


		printf("+");

		for (x = 0; x<WIDTH; x++)

			printf("%s-%s+", dashing, dashing);

		printf("\n");

	}


	printf(" ");

	for (x = 0; x<WIDTH; x++)

		printf("%s%d%s ", spacing, (x>8) ? (x + 1) / 10 : x + 1, spacing);

	if (WIDTH > 9) {

		printf("\n ");

		for (x = 0; x<WIDTH; x++)

			printf("%s%c%s ", spacing, (x>8) ? '0' + (x + 1) - ((x + 1) / 10) * 10 : ' ',

				spacing);

	}

	printf("\n\n");

}


/**

* @function print_dot

*

* dot(.) 하나를 출력한다.

* c4_poll함수에서 시간의 흐름에 따라 dot(.)을 출력하기 위해 사용된다.

*/


static void

print_dot(void)

{

	printf(".");

	fflush(stdout);

}









