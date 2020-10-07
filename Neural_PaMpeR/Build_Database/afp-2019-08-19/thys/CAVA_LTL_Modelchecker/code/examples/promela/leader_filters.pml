#define TT 1
#define FF 0

#ifndef N
    #define N 4
    #define M 4
#endif
    #define logN 5

bool elected = FF;
bool error = FF;

byte turn[logN] = 0;
bool b[logN] = 0;
bool c[logN] = 0;
byte curr[N] = 0;

bool L_1[N] = TT;
bool L_2[N] = FF;
bool L_3[N] = FF;
bool L_4[N] = FF;
bool L_5[N] = FF;
bool L_8[N] = FF;
bool L_9[N] = FF;

proctype process(int n) {
    do 
        :: atomic { L_1[n] -> turn[curr[n]] = n + 1; L_1[n] = FF; L_2[n] = TT }
        :: atomic { L_2[n] && ! b[curr[n]] -> L_2[n] = FF; L_3[n] = TT }
        :: atomic { L_3[n] -> b[curr[n]] = TT; L_3[n] = FF; L_4[n] = TT }
        :: atomic { L_4[n] -> if
                                :: turn[curr[n]] == n + 1 -> L_4[n] = FF; L_8[n] = TT
                                :: turn[curr[n]] != n + 1 -> L_4[n] = FF; L_5[n] = TT
                              fi }
        :: atomic { L_5[n] -> c[curr[n]] = TT; b[curr[n]] = FF; L_5[n] = FF }
        :: atomic { L_8[n] -> if 
                                :: curr[n] == 0 -> curr[n]++; L_8[n] = FF; L_1[n] = TT
                                :: curr[n] > 0 && ! c[curr[n] - 1] -> L_8[n] = FF; L_9[n] = TT
                                :: curr[n] > 0 && c[curr[n] - 1] -> curr[n]++; L_8[n] = FF; L_1[n] = TT
                              fi }
        :: atomic { L_9[n] && elected -> error = TT; L_9[n] = FF }
        :: atomic { L_9[n] -> elected = TT; L_9[n] = FF }
    od
}

init {
    short i;

    atomic {
        do
            :: i < N -> run process(i); i++
            :: else -> break
        od
    }
}

ltl triv { [] true }
ltl error { [] (! error) }
ltl elected { [] <> elected }
