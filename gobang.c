/*
五子棋的主要思路为使用极大极小搜索，并利用alpha-beta剪枝算法进行了优化
此外通过启发式评估函数让剪枝可发挥更大的作用，并减小每个节点所需要搜索的着法数，一定程度上牺牲了单层的思考能力，从而增加搜索层数
还使用置换表缓存搜索结果，并用主要变例搜索对alpha-beta剪枝进行了一定的优化，但对总体的棋力提升不明显，并可能导致某些bug
*/

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define SIZE 15
#define CHARSIZE 3
#define STRSIZE 10
//对各种棋形进行评分
#define SCORE_5 1000000
#define SCORE_4 10000
#define SCORE_3 100
#define SCORE_2 10
#define SCORE_L4 100000
#define SCORE_L3 1000
#define SCORE_L2 100
#define SCORE_L1 10

#define INFINITY 1000000000
//用于Zobrist缓存的标记
#define HASHEXACT 0	
#define HASHALPHA 1
#define HASHBETA 2
#define HASHEMPTY 3
#define UNKNOWN  2100000000
#define TABLESIZE 32768UL



typedef unsigned long uint64;

// 棋盘使用的是UTF8编码，每一个中文字符占用3个字节。

// 空棋盘模板
char arrayForEmptyBoard[SIZE][SIZE * CHARSIZE + 1] =
	{
		"┏┯┯┯┯┯┯┯┯┯┯┯┯┯┓",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┠┼┼┼┼┼┼┼┼┼┼┼┼┼┨",
		"┗┷┷┷┷┷┷┷┷┷┷┷┷┷┛"};
// 此数组存储用于显示的棋盘
char arrayForDisplayBoard[SIZE][SIZE * CHARSIZE + 1];

char play1Pic[] = "●"; // 黑棋子;
char play1CurrentPic[] = "▲";

char play2Pic[] = "◎"; // 白棋子;
char play2CurrentPic[] = "△";

// 此数组用于记录当前的棋盘的格局
int arrayForInnerBoardLayout[SIZE][SIZE];
//该数组用于记录搜索树的棋盘格局
int arrayForFuture[SIZE][SIZE];
//该数组给出空棋盘各个点的初始分
int arrayForBasicScore[SIZE][SIZE]=	
{
	{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
	{0,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
	{0,1,2,2,2,2,2,2,2,2,2,2,2,1,0},
	{0,1,2,3,3,3,3,3,3,3,3,3,2,1,0},
	{0,1,2,3,4,4,4,4,4,4,4,3,2,1,0},
	{0,1,2,3,4,5,5,5,5,5,4,3,2,1,0},
	{0,1,2,3,4,5,6,6,6,5,4,3,2,1,0},
	{0,1,2,3,4,5,6,7,6,5,4,3,2,1,0},
	{0,1,2,3,4,5,6,6,6,5,4,3,2,1,0},
	{0,1,2,3,4,5,5,5,5,5,4,3,2,1,0},
	{0,1,2,3,4,4,4,4,4,4,4,3,2,1,0},
	{0,1,2,3,3,3,3,3,3,3,3,3,2,1,0},
	{0,1,2,2,2,2,2,2,2,2,2,2,2,1,0},
	{0,1,1,1,1,1,1,1,1,1,1,1,1,1,0},
	{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
};
//该数组用于记录某一点在新落一子之前的评分
int arrayForScore[SIZE][SIZE][4];

//生成两个64位随机数二维数组，分别代表白棋落子和黑棋落子
uint64 Zobrist[SIZE][SIZE][2];
//键值，用于标记当前局面
uint64 Zobristkey;
//定义散列项的内容
typedef struct TranslationTable
{
	uint64 key;
	int depth;
	int value;
	int flag;
	int move[2];
} hash;
//置换表
hash hashtable[TABLESIZE];

//用于存储四个方向的棋形
char model[4][12];
//评估当前局面下我方分数和敌方分数
int myscore,enemyscore;
//记录经过搜索后得出的最好着法
int beststep[2];

//记录总步数
int steps;
//记录深度
int deep;
int enemyfive;
//记录最大搜索深度
int DEPTH;
//每个节点最多搜索的位置数
int MAXSTEP;
//记录搜索所用的时间
int timeout;

int mode = 0;//决定当前模式
int offensive = 1;//决定人机模式的先手

int player = 1; // 决定当前棋手是谁

struct site
{
	int x;
	int y;
};
struct snode
{
	int x;
	int y;
	int value;
	struct snode *next;
};

clock_t begin,end;
double duration;

typedef struct snode * stepList;


void start();

void initRecordBorard(void);
void innerLayoutToDisplayArray(void);
void displayBoard(void);
void display(int, int);

struct site human(void);
struct site robot(void);

void isWinner(int,int);

void isOverline(int,int,int [][SIZE]);
void isDouble3(int,int);
void isDouble4(int,int);

int liveThreeNum(int,int,int array[][SIZE]);
int threeNum(int,int,int array[][SIZE]);
int liveFourNum(int,int,int array[][SIZE]);
int fourNum(int,int,int array[][SIZE]);
int fiveNum(int,int,int array[][SIZE]);
int liveTwoNum(int,int,int [][SIZE]);
int twoNum(int,int,int [][SIZE]);
int liveOneNum(int,int,int [][SIZE]);

int isThreeW(int,int,int,int,int array[][SIZE]);
int isThree(int,int,int,int,int array[][SIZE]);
int isFourW(int,int,int,int,int array[][SIZE]);
int isFour(int,int,int,int,int array[][SIZE]);
int isFive(int,int,int,int,int array[][SIZE]);
int isTwoW(int,int,int,int,int array[][SIZE]);
int isTwo(int,int,int,int,int array[][SIZE]);
int isOneW(int,int,int,int,int [][SIZE]);


int evaluate(int,int);
stepList generator(void);
int minmax(int depth,int alpha,int beta);

void initialZobrist(void);
uint64 RANDOM(void);
int SearchHash(int depth,int alpha,int beta);
void RecordHash(int val,int depth,int hashflag);

int main()
{
	struct site coordinate;
	int i,j;
	start();
	initialZobrist();
	if (player!=0)
	{
		initRecordBorard(); // 初始化一个空棋盘
		innerLayoutToDisplayArray();
		displayBoard();
	}
	while (player > 0)
	{
		if (mode==2)
		{
			if (offensive==player)		//offensive=2,则机器先手
				coordinate=human();
			else
				coordinate=robot();
		} else if (mode==1)
		{
			coordinate = human();
		}
		display(coordinate.x,coordinate.y);
		isWinner(coordinate.x,coordinate.y);				//判断是否胜利
		if (offensive==1)									//判断是否为禁手
		{
			isOverline(coordinate.x,coordinate.y,arrayForInnerBoardLayout);
			isDouble3(coordinate.x,coordinate.y);
			isDouble4(coordinate.x,coordinate.y);
		}
		printf("%f\n",duration);
		//落子后刷新当前局面分数
		evaluate(coordinate.x,coordinate.y);
		for(i=0;i<SIZE;i++)
			for(j=0;j<SIZE;j++)
				arrayForFuture[i][j]=arrayForInnerBoardLayout[i][j];
		evaluate(coordinate.x,coordinate.y);

		Zobristkey=Zobristkey^Zobrist[coordinate.x][coordinate.y][player-1];
		printf("%d%c\n",coordinate.x+1,coordinate.y+'A');						//打印落子位置
		steps++;
		if (steps>=225)		//棋子下满，结束
		{
			return 0;
		}
		if (player!=0)			//一次循环结束后改变落子方
		{
			player=player^3;
		}
	}
	return 0;
}

//开始，玩家选择人人对战或者人机对战
void start()
{
	char c;
	int result;
	printf("Author:Zhu Xianan\n");
	getchar();
	result=system("clear");
	printf("Please choose a mode(enter 0 to quit):\n");
	printf("1:human vs human\n");
	printf("2:human vs robot\n");

	while ((c=getchar())!='0' && c!='1' && c!='2')
		printf("Please enter 0 or 1 or 2\n");
	getchar();
	if (c=='0')
	{
		player=0;
		return;
	}else
		mode = c - '0';
	
	if (mode == 2)
	{
		printf("Please determine who is on the offensive(enter 0 to quit):\n");
		printf("1:human\n");
		printf("2:robot\n");
		
		while ((c=getchar())!='0' && c!='1' && c!='2')
			printf("Please enter 0 or 1 or 2\n");
		if (c == '0')
		{
			player = 0;
			return;
		}
		else
			offensive = c-'0';
	}
}


// 初始化一个空棋盘格局
void initRecordBorard(void)
{
	// 通过双重循环，将arrayForInnerBoardLayout清0
	int i, j;
	for (i = 0; i < SIZE; i++)
		for (j = 0; j < SIZE; j++)
			arrayForInnerBoardLayout[i][j] = 0;
}

// 将arrayForInnerBoardLayout中记录的棋子位置，转化到arrayForDisplayBoard中
void innerLayoutToDisplayArray(void)
{
	// 第一步：将arrayForEmptyBoard中记录的空棋盘，复制到arrayForDisplayBoard中
	int i, j, k;
	for (i = 0; i < SIZE; i++)
		for (j = 0; j <= SIZE * CHARSIZE; j++)
			arrayForDisplayBoard[i][j] = arrayForEmptyBoard[i][j];

	// 第二步：扫描arrayForInnerBoardLayout，当遇到非0的元素，将●或者◎复制到arrayForDisplayBoard的相应位置上
	// 注意：arrayForDisplayBoard所记录的字符是中文字符，每个字符占2个字节。●和◎也是中文字符，每个也占2个字节。

	for (i = 0; i < SIZE; i++)
		for (j = 0; j < SIZE; j++)
		{ // 若元素为正数，说明是已经下完的棋子，用圆形；若为负数，是正在下的棋子，用三角形
			if (arrayForInnerBoardLayout[i][j] == 1)
			{
				for (k = 0; k < CHARSIZE; k++)
					arrayForDisplayBoard[SIZE - 1 - i][j * CHARSIZE + k] = play1Pic[k];
			}
			else if (arrayForInnerBoardLayout[i][j] == 2)
			{
				for (k = 0; k < CHARSIZE; k++)
					arrayForDisplayBoard[SIZE - 1 - i][j * CHARSIZE + k] = play2Pic[k];
			}
			else if (arrayForInnerBoardLayout[i][j] == -1)
			{
				for (k = 0; k < CHARSIZE; k++)
					arrayForDisplayBoard[SIZE - 1 - i][j * CHARSIZE + k] = play1CurrentPic[k];
				arrayForInnerBoardLayout[i][j] = 1;
			}
			else if (arrayForInnerBoardLayout[i][j] == -2)
			{
				for (k = 0; k < CHARSIZE; k++)
					arrayForDisplayBoard[SIZE - 1 - i][j * CHARSIZE + k] = play2CurrentPic[k];
				arrayForInnerBoardLayout[i][j] = 2;
			}
		}
}

// 显示棋盘格局
void displayBoard(void)
{
	int i;
	int result;
	// 第一步：清屏
	result=system("clear"); // 清屏
	// 第二步：将arrayForDisplayBoard输出到屏幕上
	for (i = 0; i < SIZE; i++)
	{
		printf("%2d %s\n", SIZE - i, arrayForDisplayBoard[i]);
	}

	// 第三步：输出最下面的一行字母A B ....
	printf("  ");
	for (i = 0; i < SIZE; i++)
		printf(" %c", i + 'A');
	printf("\n");
}



void display(int line, int row)
{
	if (player == 1)
	{
		arrayForInnerBoardLayout[line][row] = -1; // 对现输入的位置赋负值
	}
	else if (player == 2)
	{
		arrayForInnerBoardLayout[line][row] = -2;
	}
	else if (player == 0)
	{
		return;
	}

	innerLayoutToDisplayArray();
	displayBoard();
}

//若出现五子或以上相连的情况，宣布player胜利，结束游戏
void isWinner(int x,int y)
{
	int i;

	if (player==0)
		return;

	if (fiveNum(x,y,arrayForInnerBoardLayout)>0)
	{	
		printf("Winner is player%d\n",player);
		player=0;
	}
	
}

//判断是否为长连
void isOverline(int x,int y,int array[][SIZE])
{
	if (player==0)
		return;
	int i;
	int linkNumL=0;
	int linkNumV=0;
	int linkNumU=0;
	int linkNumD=0;
	for (i=0;array[x+i][y]==player && x+i<SIZE;i++)
		linkNumL++;
	for (i=1;array[x-i][y]==player && x-i>-1;i++)
		linkNumL++;

	for (i=0;array[x][y+i]==player && y+i<SIZE;i++)
		linkNumV++;
	for (i=1;array[x][y-i]==player && y-i>-1;i++)
		linkNumV++;
	
	for (i=0;array[x+i][y+i]==player && x+i<SIZE && y+i<SIZE;i++)
		linkNumU++;
	for (i=1;array[x-i][y-i]==player && x-i>-1 && y-i>-1;i++)
		linkNumU++;
	
	for (i=0;array[x+i][y-i]==player && x+i<SIZE && y-i>-1;i++)
		linkNumD++;
	for (i=1;array[x-i][y+i]==player && x-i>-1 && y+i<SIZE;i++)
		linkNumD++;
	if (player==1)
	{
		if (linkNumL>5 || linkNumV>5 || linkNumU >5 || linkNumD >5)
		{
			printf("Forbidden Step:Overline!\n");
			player = 0;
		}
	}
}

//判断是否形成三三禁手
void isDouble3(int x,int y)
{
	if (player==0)
		return;
	if (liveThreeNum(x,y,arrayForInnerBoardLayout)>1 && player==1)
	{
		player=0;
		printf("Forbidden Step:Double Three!\n");
	}
}
//判断是否形成四四禁手
void isDouble4(int x,int y)
{
	if (player==0)
		return;
	
	if (fourNum(x,y,arrayForInnerBoardLayout)>1 && player==1)
	{
		player=0;
		printf("Forbidden Step:Double Four!\n");
	}
}

//某点活三数
int liveThreeNum(int x,int y,int array[][SIZE])
{
	int live3num;
	live3num=isThreeW(x,y,1,0,array)+isThreeW(x,y,0,1,array)+isThreeW(x,y,1,1,array)+isThreeW(x,y,1,-1,array);
	return live3num;
}
//某点冲四和活四数
int fourNum(int x,int y,int array[][SIZE])
{
	int fournum;
	fournum=isFour(x,y,0,1,array)+isFour(x,y,1,0,array)+isFour(x,y,1,1,array)+isFour(x,y,1,-1,array);
	return fournum;
}
//某点连五数
int fiveNum(int x,int y,int array[][SIZE])
{
	int fivenum;
	fivenum=isFive(x,y,0,1,array)+isFive(x,y,1,0,array)+isFive(x,y,1,1,array)+isFive(x,y,1,-1,array);
	return fivenum;
}

//判断单个方向上活三的数量
int isThreeW(int x,int y,int line,int row,int array[][SIZE])
{
	char model[12];
	int liveThree=0;
	int i;

	for (i=0;i<6;i++)
	{
		if (x+i*line>=SIZE || y+i*row>=SIZE)
			model[i+5]=2+'0';
		else
		{	
			model[i+5]=array[x+i*line][y+i*row]+'0';
			if (model[i+5]!='0')
				model[i+5]=(model[i+5]==(player+'0'))?'1':'2';
		}
		if (x-i*line<0 || y-i*row<0)
			model[-i+5]=2+'0';
		else
		{
			model[-i+5]=array[x-i*line][y-i*row]+'0';
			if (model[-i+5]!='0')
				model[-i+5]=(model[-i+5]==(player+'0'))?'1':'2';
		}
	}
	model[11]='\0';
	if (strstr(model,"00111000")!=NULL
		||strstr(model,"00111002")!=NULL
		||strstr(model,"20111000")!=NULL
		||strstr(model,"20111002")!=NULL
		||strstr(model,"00011100")!=NULL
		||strstr(model,"20011100")!=NULL
		||strstr(model,"00011102")!=NULL
		||strstr(model,"20011102")!=NULL
		||strstr(model,"00101100")!=NULL
		||strstr(model,"00101102")!=NULL
		||strstr(model,"20101100")!=NULL
		||strstr(model,"20101102")!=NULL
		||strstr(model,"00110100")!=NULL
		||strstr(model,"00110102")!=NULL
		||strstr(model,"20110100")!=NULL
		||strstr(model,"20110102")!=NULL)
		liveThree=1;
	return liveThree;
}

//判断单个方向上存在的冲四和活四的数量
int isFour(int x,int y,int line,int row,int array[][SIZE])
{
	char model[12];
	int Four=0;
	int liveFour=0;
	int i;


	for (i=0;i<6;i++)
	{
		if (x+i*line>=SIZE || y+i*row>=SIZE)
			model[i+5]=2+'0';
		else
		{	
			model[i+5]=array[x+i*line][y+i*row]+'0';
			if (model[i+5]!='0')
				model[i+5]=(model[i+5]==(player+'0'))?'1':'2';
		}
		if (x-i*line<0 || y-i*row<0)
			model[-i+5]=2+'0';
		else
		{
			model[-i+5]=array[x-i*line][y-i*row]+'0';
			if (model[-i+5]!='0')
				model[-i+5]=(model[-i+5]==(player+'0'))?'1':'2';
		}
	}
	model[11]='\0';

	if (strstr(model,"011110")!=NULL
		&& strstr(model,"10111101")==NULL
		&& strstr(model,"1011110")==NULL
		&& strstr(model,"0111101")==NULL)
		liveFour=1;

	if (strstr(model,"01110101110")!=NULL
		|| strstr(model,"0110110110")!=NULL
		|| strstr(model,"010111010")==(model+1)
		|| strstr(model,"21110101112")!=NULL
		|| strstr(model,"2110110112")!=NULL
		|| strstr(model,"210111012")==(model+1)
		|| strstr(model,"21110101110")!=NULL
		|| strstr(model,"2110110110")!=NULL
		|| strstr(model,"210111010")==(model+1)
		|| strstr(model,"01110101112")!=NULL
		|| strstr(model,"0110110112")!=NULL
		|| strstr(model,"010111012")==(model+1))
		Four=2;
	else if (liveFour==0
			&& (strstr(model,"0101110")!=NULL
			|| strstr(model,"0111010")!=NULL
			|| strstr(model,"0110110")!=NULL
			|| strstr(model,"0111100")!=NULL
			|| strstr(model,"0011110")!=NULL
			|| strstr(model,"2101112")!=NULL
			|| strstr(model,"2111012")!=NULL
			|| strstr(model,"2110112")!=NULL
			|| strstr(model,"2111102")!=NULL
			|| strstr(model,"2011112")!=NULL
			|| strstr(model,"0101112")!=NULL
			|| strstr(model,"0111012")!=NULL
			|| strstr(model,"0110112")!=NULL
			|| strstr(model,"0111102")!=NULL
			|| strstr(model,"0011112")!=NULL
			|| strstr(model,"2101110")!=NULL
			|| strstr(model,"2111010")!=NULL
			|| strstr(model,"2110110")!=NULL
			|| strstr(model,"2011110")!=NULL
			|| strstr(model,"2111100")!=NULL))
		Four=1;
	return (Four+liveFour);
}

//判断单个方向上存在的连五的数量
int isFive(int x,int y,int line,int row,int array[][SIZE])
{
	int Five=0;
	int count=0;
	int i;

	for (i=0;array[x+i*line][y+i*row]==player && x+i*line<SIZE && y+i*row<SIZE;i++)
		count++;
	for (i=1;array[x-i*line][y-i*row]==player && x-i*line>=0 && y-i*row>=0;i++)
		count++;
	if (count>=5 && (player==2 || count==5))
		Five=1;

	return Five;
}

//读取人类的落子
struct site human(void)
{
	struct site coordinate;
	int isQuit = 0;
	int status = 0;
	int line, row;
	char input[STRSIZE];
	int result;
	while (status == 0) // 通过循环判断输入的是否为合法的格式
	{
		result=scanf("%s", input);
		if (strcmp(input, "quit") == 0) // 判断是否输入quit
			isQuit = 1;
		if (isQuit == 1) // 若输入quit，退出主函数while循环
		{
			player = 0;
			break;
		}
		line = atoi(input) - 1; // 若格式正确，则将读入的数字赋给line
		if (line > 8)			// 若格式正确，读入第二位或第三位的字母
			row = input[2] - 'a';
		else
			row = input[1] - 'a';

		// 判断是否超出棋盘或重复
		if (arrayForInnerBoardLayout[line][row] != 0 || line < 0 || line >= SIZE || row < 0 || row >= SIZE)
			printf("error\n");
		else
			status = 1;
	}

	coordinate.x = line;
	coordinate.y = row;
	
	return coordinate;
}

//读取机器的落子
struct site robot()
{
	struct site coordinate;
	int status=0;
	int i;
	int bestscore;
	int depth;
	int alpha=-INFINITY;
	int beta=INFINITY;
	//在每次搜索之前将置换表设置为可清空的状态
	for(i=0;i<TABLESIZE;i++)
	{
		hashtable[i].flag=HASHEMPTY;
	}

	begin=clock();
	DEPTH = 4;
	MAXSTEP = 20;
	timeout = 0;
	//进行深度递增的搜索
	for (deep = 2; deep <= DEPTH; deep += 2)
	{
		bestscore = minmax(deep, alpha, beta);
		if (timeout == 0)
		{
			coordinate.x = beststep[0];
			coordinate.y = beststep[1];
		}
		if (bestscore >= 5 * SCORE_5 || enemyfive == 1 || timeout == 1)
		{
			enemyfive = 0;
			break;
		}
	}
	end=clock();
	duration=(double)(end-begin)/CLOCKS_PER_SEC;
	
	
	return coordinate;
}
//通过递归调用，进行极大极小搜索，可进行alpha-beta剪枝
//搜索和评价函数仍存在一定bug，包括先手主动触发四四禁手，以及某些情况下不对冲四和活三进行拦截
int minmax(int depth,int alpha,int beta)
{
    stepList plist=NULL,q;
	int isPV=0;
    int score;
	int mytempscore,enemytempscore;
    int fivenum;
	int val;
	int hashflag=HASHALPHA;

	//若此时的局面在置换表中有存储，则直接返回表中的值
	if((val=SearchHash(depth,alpha,beta))!=UNKNOWN)
	{
		return val;
	}
	

    if (depth==0)
    {
		RecordHash(myscore-enemyscore,depth,HASHEXACT);
        return myscore-enemyscore;
    }
    plist=generator();
	
    while (plist!=NULL)
    {
		if (clock()-begin>14500000)
		{
			timeout=1;
		}
		mytempscore=myscore;
		enemytempscore=enemyscore;
		evaluate(plist->x,plist->y);
        arrayForFuture[plist->x][plist->y]=player;						//以上四行为理解为走出一步，即生成一个新的节点
    	Zobristkey=Zobristkey^Zobrist[plist->x][plist->y][player-1];	//更新Zobrist键值
		fivenum=evaluate(plist->x,plist->y);							//评判该步是否可成五
		if (fivenum!=1)
		{
			//若扫描到最后一层时有评分较大的着法，则额外扫描4层
			if (plist->value>=30 && depth==1 && MAXSTEP!=10 && timeout==0 && steps<35)
			{
			depth=5;
			MAXSTEP=10;
			}

			player=(player ^ 3);
			//进行主要变例搜索
			if (isPV)
			{
				score=-minmax(depth-1,-alpha-1,-alpha);
				if ((score>alpha)&&(score<beta))
				{
					score=-minmax(depth-1,-beta,-alpha);
				}
			}
			else
			{
				score=-minmax(depth-1,-beta,-alpha);
			}
			player=(player ^ 3);
		}else
		{
			//若成五，立刻将该节点打分为一个大值
			score=SCORE_5*10;
			if(deep==2 && depth==1)										//若进行两层搜索时发现敌方可成五（即当前局面出现冲四）立刻拦截
				enemyfive=1;

		}
		//复原
		arrayForFuture[plist->x][plist->y]=0;						
		Zobristkey=Zobristkey^Zobrist[plist->x][plist->y][player-1];
		myscore=mytempscore;
		enemyscore=enemytempscore;
		if (depth==5)
		{
        	MAXSTEP=20;
			depth=1;
		}
		//进行剪枝操作
		if (score>=beta)
        {
			q=plist;													//释放存储当前节点所代表位置的链表节点
        	plist=q->next;
        	free(q);
			RecordHash(beta,depth,HASHBETA);
            return beta;
        }
		if (score>alpha)
		{
			hashflag=HASHEXACT;
			alpha=score;
			isPV=1;
			if (depth==deep)
			{										//在最浅层跟据最佳分数改变最佳行走位置
            	beststep[0]=plist->x;
				beststep[1]=plist->y;
			}
		}
		q=plist;													//释放存储当前节点所代表位置的链表节点
        plist=q->next;
        free(q);
		
    }
	RecordHash(alpha,depth,hashflag);
    return alpha;
}
//启发式评估函数
stepList generator(void)
{
	int i,j;
	int k,l;
	int line,row;
	int maxstep;
    int tempvalue;
    stepList p,plist,pbegin,plast;
	int count;
    pbegin=NULL;
    plist=NULL;
	if (steps>=10)
		maxstep=MAXSTEP;
	else 
		maxstep=10;
    for (i=0;i<SIZE;i++)
    {
		
        for (j=0;j<SIZE;j++)
        {
			count=0;
			if (arrayForFuture[i][j]!=0)
				continue;
            /*judge*/
			tempvalue=0;
			for (l=0;l<4;l++)
			{
				switch (l)
                {
                case 0:line=1;row=0;break;
                case 1:line=0;row=1;break;
                case 2:line=1;row=1;break;
                case 3:line=1;row=-1;break;
                default:break;
                }
                for (k=-4;k<5;k++)
                {
                    if (i + k * line >= SIZE || j + k * row >= SIZE || i + k * line < 0 || j + k * row < 0)
                        model[l][k + 4] = 3 + '0';
                    else
                    {
                        model[l][k + 4] = arrayForFuture[i + k * line][j + k * row] + '0';
                    }
                }	//根据局面中邻近二、三、四的数量进行排序
				model[l][9]='\0';
				if (strstr(model[l],"1111")!=NULL
					||strstr(model[l],"11101")!=NULL
					||strstr(model[l],"10111")!=NULL
					||strstr(model[l],"11011")!=NULL)
					tempvalue+=40;
				else if (strstr(model[l],"111")!=NULL
					||strstr(model[l],"1101")!=NULL
					||strstr(model[l],"1011")!=NULL)
					tempvalue+=30;

				if (strstr(model[l],"2222")!=NULL
					||strstr(model[l],"22202")!=NULL
					||strstr(model[l],"20222")!=NULL
					||strstr(model[l],"22022")!=NULL)
					tempvalue+=40;
				else if (strstr(model[l],"222")!=NULL
					||strstr(model[l],"2202")!=NULL
					||strstr(model[l],"2022")!=NULL)
					tempvalue+=30;
				
				if (strstr(model[l],"0110")!=NULL
					||strstr(model[l],"0101")!=NULL
					||strstr(model[l],"1010")!=NULL)
					tempvalue+=20;
				if (strstr(model[l],"0220")!=NULL
					||strstr(model[l],"0202")!=NULL
					||strstr(model[l],"2020")!=NULL)
					tempvalue+=20;
				
			}
            tempvalue+=arrayForBasicScore[i][j];
			//生成链表并根据每个点的打分值进行从大到小的排序，最终保留下前maxstep个
			p=(stepList)malloc(sizeof(struct snode));
            p->value=tempvalue;p->x=i;p->y=j;p->next=NULL;
            if (pbegin==NULL)
            {
                pbegin=p;
				plist=pbegin;
                continue;
            }
			
            while(plist->next!=NULL && (plist->next)->value>p->value)
            {
                plist=plist->next;
            }
			
			if (plist->value>p->value)
			{
				p->next=plist->next;
				plist->next=p;
			}
			else
			{
				p->next=plist;
				pbegin=p;
			}
			plast=pbegin;
			while(plast->next!=NULL && count<maxstep)
			{
				plast=plast->next;
				count++;
			}
			if(plast->next!=NULL)
			{
				free(plast->next);
				plast->next=NULL;
			}
			plist=pbegin;
        }
    }
    return pbegin;
}
//局部评估函数，每次生成节点时刷新敌我分数
int evaluate(int x,int y)
{
    int px,py;
    int h,i;
    int j,k;
    int line,row;
    int tempscore=0;
	int liveThree,Three,liveFour,Four,Overline,Five,liveTwo,Two,One;
	int total4,totall3;
	int isfive=0;
	total4=totall3=0;
	
    for (h=0;h<4;h++)
    {
        
        for (i=-5;i<6;i++)
        {
			if (i==0 && h!=0)						//防止对中心位置进行四次次评分
				continue;
            switch (h)
            {
            case 0:px=x+i;py=y;break;
            case 1:px=x;py=y+i;break;
            case 2:px=x+i;py=y+i;break;
            case 3:px=x+i;py=y-i;break;
            default:break;
            }

            if (px<SIZE && py<SIZE && px>=0 && py>=0 && arrayForFuture[px][py]!=0)
            {
                for (j=0;j<4;j++)
                {
					if (i!=0 && j!=h)				//只考虑中心位置周围米字区域的非空白点
						continue;
					liveThree=Three=liveFour=Four=Overline=Five=liveTwo=Two=One=0;

                    switch (j)								//获取评分点周围的棋子信息
                    {
                    case 0:line=1;row=0;break;
                    case 1:line=0;row=1;break;
                    case 2:line=1;row=1;break;
                    case 3:line=1;row=-1;break;
                    default:break;
                    }
                    for (k=-5;k<6;k++)
                    {
                        if (px + k * line >= SIZE || py + k * row >= SIZE || px + k * line < 0 || py + k * row < 0)
                            model[j][k + 5] = 2 + '0';
                        else
                        {
                            model[j][k + 5] = arrayForFuture[px + k * line][py + k * row] + '0';
                            if (model[j][k + 5] != '0')
                                model[j][k + 5] = (model[j][k + 5] == (arrayForFuture[px][py] + '0')) ? '1' : '2';
                        }
                    }
                    model[j][11]='\0';

                    //利用模式串匹配评分
					if (strstr(model[j],"00111000")!=NULL
						||strstr(model[j],"00111002")!=NULL
						||strstr(model[j],"20111000")!=NULL
						||strstr(model[j],"20111002")!=NULL
						||strstr(model[j],"00011100")!=NULL
						||strstr(model[j],"20011100")!=NULL
						||strstr(model[j],"00011102")!=NULL
						||strstr(model[j],"20011102")!=NULL
						||strstr(model[j],"00101100")!=NULL
						||strstr(model[j],"00101102")!=NULL
						||strstr(model[j],"20101100")!=NULL
						||strstr(model[j],"20101102")!=NULL
						||strstr(model[j],"00110100")!=NULL
						||strstr(model[j],"00110102")!=NULL
						||strstr(model[j],"20110100")!=NULL
						||strstr(model[j],"20110102")!=NULL)
						liveThree=1;

					if (strstr(model[j],"00110101100")!=NULL
						||strstr(model[j],"00110101102")!=NULL
						||strstr(model[j],"20110101100")!=NULL
						||strstr(model[j],"20110101102")!=NULL
						||strstr(model[j],"2010110102")!=NULL
						||strstr(model[j],"2010110100")!=NULL
						||strstr(model[j],"0010110102")!=NULL
						||strstr(model[j],"0010110100")!=NULL)
						Three=2;
					else if (strstr(model[j],"2010112")!=NULL
						||strstr(model[j],"0010112")!=NULL
						||strstr(model[j],"20101101")!=NULL
						||strstr(model[j],"00101101")!=NULL
						||strstr(model[j],"2011012")!=NULL
						||strstr(model[j],"0011012")!=NULL
						||strstr(model[j],"20110101")!=NULL
						||strstr(model[j],"00110101")!=NULL
						||strstr(model[j],"2011102")!=NULL
						||strstr(model[j],"2111002")!=NULL
						||strstr(model[j],"2001112")!=NULL
						||strstr(model[j],"2111000")!=NULL
						||strstr(model[j],"0001112")!=NULL
						||strstr(model[j],"10011102")!=NULL
						||strstr(model[j],"20111001")!=NULL
						||strstr(model[j],"100111001")!=NULL)
						Three=1;

					if (strstr(model[j],"011110")!=NULL
						&& strstr(model[j],"10111101")==NULL
						&& strstr(model[j],"1011110")==NULL
						&& strstr(model[j],"0111101")==NULL)
						liveFour=1;							
					if (strstr(model[j],"01110101110")!=NULL
						|| strstr(model[j],"0110110110")!=NULL
						|| strstr(model[j],"010111010")==(model[j]+1)
						|| strstr(model[j],"21110101112")!=NULL
						|| strstr(model[j],"2110110112")!=NULL
						|| strstr(model[j],"210111012")==(model[j]+1)
						|| strstr(model[j],"21110101110")!=NULL
						|| strstr(model[j],"2110110110")!=NULL
						|| strstr(model[j],"210111010")==(model[j]+1)
						|| strstr(model[j],"01110101112")!=NULL
						|| strstr(model[j],"0110110112")!=NULL
						|| strstr(model[j],"010111012")==(model[j]+1))
						Four=2;
					else if (liveFour==0
							&& (strstr(model[j],"0101110")!=NULL
							|| strstr(model[j],"0111010")!=NULL
							|| strstr(model[j],"0110110")!=NULL
							|| strstr(model[j],"0111100")!=NULL
							|| strstr(model[j],"0011110")!=NULL
							|| strstr(model[j],"2101112")!=NULL
							|| strstr(model[j],"2111012")!=NULL
							|| strstr(model[j],"2110112")!=NULL
							|| strstr(model[j],"2111102")!=NULL
							|| strstr(model[j],"2011112")!=NULL
							|| strstr(model[j],"0101112")!=NULL
							|| strstr(model[j],"0111012")!=NULL
							|| strstr(model[j],"0110112")!=NULL
							|| strstr(model[j],"0111102")!=NULL
							|| strstr(model[j],"0011112")!=NULL
							|| strstr(model[j],"2101110")!=NULL
							|| strstr(model[j],"2111010")!=NULL
							|| strstr(model[j],"2110110")!=NULL
							|| strstr(model[j],"2011110")!=NULL
							|| strstr(model[j],"2111100")!=NULL))
						Four=1;

					if (strstr(model[j],"11111")!=NULL
						&& (strstr(model[j],"111111")==NULL || player==2))
						Five=1;

					if (strstr(model[j],"0101010")==(model[j]+2)
						||strstr(model[j],"1001001")==(model[j]+2))
						liveTwo=2;
					else if (liveFour==0 && liveThree==0 && Four==0 && Three==0
						&& (strstr(model[j],"0110")==(model[j]+3)
						||strstr(model[j],"01010")==(model[j]+2)
						||strstr(model[j],"1001")==(model[j]+2)
						||strstr(model[j],"0110")==(model[j]+4)
						||strstr(model[j],"01010")==(model[j]+4)
						||strstr(model[j],"1001")==(model[j]+5)))
						liveTwo=1;

					if (Four==0 && Three==0
						&& (strstr(model[j],"21012")==(model[j]+4)
						||strstr(model[j],"21100")==(model[j]+4)
						||strstr(model[j],"00112")==(model[j]+3)
						||strstr(model[j],"21102")==(model[j]+4)
						||strstr(model[j],"20112")==(model[j]+3)
						||strstr(model[j],"21012")==(model[j]+2)
						||strstr(model[j],"21100")==(model[j]+3)
						||strstr(model[j],"00112")==(model[j]+2)
						||strstr(model[j],"21102")==(model[j]+3)
						||strstr(model[j],"20112")==(model[j]+2)))
						Two=1;
					
					if (liveFour==0 && liveThree==0 && Four==0 && Three==0 && liveTwo==0
						&& strstr(model[j],"010")==(model[j]+4))
						One=1;
					if (i==0)
					{
						totall3+=liveThree;
						total4+=liveFour+Four;
						if(Five==1)
							isfive=1;

					}
					tempscore=SCORE_5*Five+SCORE_L4*liveFour+SCORE_L3*liveThree+SCORE_L2*liveTwo
							  +SCORE_L1*One+SCORE_4*Four+SCORE_3*Three+SCORE_2*Two;
					
					/*对敌我局势进行评分，一次评分需在minmax中调用两次evaluate，第一次将未落子时局部分数记录，第二次局部分数减去原先的，加上落子后的*/
					if (arrayForFuture[x][y]!=0)
					{
						if (arrayForFuture[px][py]==offensive)
						{
							enemyscore=enemyscore+tempscore-arrayForScore[px][py][j];
						}else
						{
							myscore=myscore+tempscore-arrayForScore[px][py][j];
						}
					}else
						arrayForScore[px][py][j]=tempscore;
					
                }

            }
        }
    }
	if(arrayForFuture[x][y]==0)
	{
		arrayForScore[x][y][0]=0;
		arrayForScore[x][y][1]=0;
		arrayForScore[x][y][2]=0;
		arrayForScore[x][y][3]=0;
	}
	else if ((totall3>1 || total4>1) && arrayForFuture[x][y]==1 && isfive!=1)
	{
		if (offensive==1)
			enemyscore=-INFINITY;
		else
			myscore=-INFINITY;
	}
	return isfive;
}

//Zobrist缓存部分

//生成64位随机数
uint64 RANDOM(void)
{
	return ((uint64)rand())^((uint64)rand()<<32);
}
//初始化键值和Zobrist数组
void initialZobrist(void)
{
	int i,j,k; 
	for(k=0;k<2;k++)
	{
		for(i=0;i<SIZE;i++)
		{
			for(j=0;j<SIZE;j++)
			{
				Zobrist[i][j][k]=RANDOM();
			}
		}
	}
	Zobristkey=RANDOM();
}
//利用键值在置换表中搜索
int SearchHash(int depth,int alpha,int beta)
{
	hash *transtable=&hashtable[Zobristkey & (TABLESIZE-1)];
	if (transtable->key==Zobristkey)
	{
		if (transtable->depth==depth)
		{
			if (transtable->flag==HASHEXACT)
			{
				return transtable->value;
			}
			if ((transtable->flag==HASHALPHA)&&(transtable->value<=alpha))
			{
				return alpha;
			}
			if ((transtable->flag==HASHBETA)&&(transtable->value>=beta))
			{
				return beta;
			}
		}
	}

	return UNKNOWN;
}
//记录新的散列项
void RecordHash(int val,int depth,int hashflag)
{
	hash *transtable=&hashtable[Zobristkey & (TABLESIZE-1)];
	if (transtable->flag!=HASHEMPTY && transtable->depth>depth)
	{
		return;
	}
	transtable->depth=depth;
	transtable->value=val;
	transtable->key=Zobristkey;
	transtable->flag=hashflag;
}