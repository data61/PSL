#define TT 1
#define FF 0

#ifndef N
    #define N 5
#endif

bool free[N] = TT; /* fork n is free */
bool eat[N] = FF; /* phil n eats */
bool one[N] = FF; /* phil n has taken one fork */

#define next (n + 1) % N

proctype phil(int n) {
    do
        :: atomic { (! eat[n]) && free[n] -> one[n] = TT; free[n] = FF }
        :: atomic { one[n] && free[next] -> one[n] = FF; free[next] = FF; eat[n] = TT }
        :: atomic { eat[n] -> free[n] = TT; free[next] = TT; eat[n] = FF }
    od
}

init {
    short i = 0;
    atomic {
        for (i in free) { run phil(i) }
    }
}

ltl triv { ! (true U false) }
ltl free_one { ! ([] (free[2] <-> one[2])) }
ltl not_so_triv { ! (<> (eat[1] && eat[2])) } 
ltl test {!([] <> (eat[1] & free[1]))}
ltl bla { [] free[2] }
