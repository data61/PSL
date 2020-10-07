#define TT 1
#define FF 0

#ifndef N
    #define N 5
#endif

bool ready = TT;
bool readers_active = FF;
bool writers_active = FF;
bool q_error = FF;

bool reading[N] = FF;
bool writing[N] = FF;

int active_readers = 0;

proctype reader(int n) {
    do
        :: atomic { ready -> ready = FF; readers_active = TT }
        :: atomic { readers_active && (! reading[n]) -> active_readers++; reading[n] = TT }
        :: atomic { readers_active && reading[n] -> active_readers--; reading[n] = FF }
        :: atomic { readers_active && active_readers == 0 -> readers_active = FF; ready = TT }
    od
}

proctype writer(int n) {
    do
        :: atomic { ready -> ready = FF; writers_active = TT; writing[n] = TT }
        :: atomic { readers_active && writing[n] -> readers_active = FF; q_error = TT; writing[n] = FF }
        :: atomic { writers_active && writing[n] -> writers_active = FF; ready = TT; writing[n] = FF }
    od
}

init {
    int i;

    atomic {
        do
            :: i < N ->  run reader(i);  run writer(i); i++
            :: else -> break
        od
    }
}

ltl triv { [] true }
ltl q_error { [] (! q_error) }
ltl ar { [] ( active_readers >= 0 ) }
ltl test { [] ( ready U (writers_active || readers_active) ) }
