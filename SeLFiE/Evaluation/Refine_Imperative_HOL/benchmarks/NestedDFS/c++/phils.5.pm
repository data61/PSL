#define one0  (phil_0@one)
#define eat0  (phil_0@eat)
byte fork[12];


active proctype phil_0() { 

think: if
::  d_step {fork[0]==0;fork[0] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[1]==0;fork[1] = 1;}  goto eat; 

fi;
eat: if
:: fork[0] = 0; goto finish; 

fi;
finish: if
:: fork[1] = 0; goto think; 

fi;
}

active proctype phil_1() { 

think: if
::  d_step {fork[1]==0;fork[1] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[2]==0;fork[2] = 1;}  goto eat; 

fi;
eat: if
:: fork[1] = 0; goto finish; 

fi;
finish: if
:: fork[2] = 0; goto think; 

fi;
}

active proctype phil_2() { 

think: if
::  d_step {fork[2]==0;fork[2] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[3]==0;fork[3] = 1;}  goto eat; 

fi;
eat: if
:: fork[2] = 0; goto finish; 

fi;
finish: if
:: fork[3] = 0; goto think; 

fi;
}

active proctype phil_3() { 

think: if
::  d_step {fork[3]==0;fork[3] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[4]==0;fork[4] = 1;}  goto eat; 

fi;
eat: if
:: fork[3] = 0; goto finish; 

fi;
finish: if
:: fork[4] = 0; goto think; 

fi;
}

active proctype phil_4() { 

think: if
::  d_step {fork[4]==0;fork[4] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[5]==0;fork[5] = 1;}  goto eat; 

fi;
eat: if
:: fork[4] = 0; goto finish; 

fi;
finish: if
:: fork[5] = 0; goto think; 

fi;
}

active proctype phil_5() { 

think: if
::  d_step {fork[5]==0;fork[5] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[6]==0;fork[6] = 1;}  goto eat; 

fi;
eat: if
:: fork[5] = 0; goto finish; 

fi;
finish: if
:: fork[6] = 0; goto think; 

fi;
}

active proctype phil_6() { 

think: if
::  d_step {fork[6]==0;fork[6] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[7]==0;fork[7] = 1;}  goto eat; 

fi;
eat: if
:: fork[6] = 0; goto finish; 

fi;
finish: if
:: fork[7] = 0; goto think; 

fi;
}

active proctype phil_7() { 

think: if
::  d_step {fork[7]==0;fork[7] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[8]==0;fork[8] = 1;}  goto eat; 

fi;
eat: if
:: fork[7] = 0; goto finish; 

fi;
finish: if
:: fork[8] = 0; goto think; 

fi;
}

active proctype phil_8() { 

think: if
::  d_step {fork[8]==0;fork[8] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[9]==0;fork[9] = 1;}  goto eat; 

fi;
eat: if
:: fork[8] = 0; goto finish; 

fi;
finish: if
:: fork[9] = 0; goto think; 

fi;
}

active proctype phil_9() { 

think: if
::  d_step {fork[9]==0;fork[9] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[10]==0;fork[10] = 1;}  goto eat; 

fi;
eat: if
:: fork[9] = 0; goto finish; 

fi;
finish: if
:: fork[10] = 0; goto think; 

fi;
}

active proctype phil_10() { 

think: if
::  d_step {fork[10]==0;fork[10] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[11]==0;fork[11] = 1;}  goto eat; 

fi;
eat: if
:: fork[10] = 0; goto finish; 

fi;
finish: if
:: fork[11] = 0; goto think; 

fi;
}

active proctype phil_11() { 

think: if
::  d_step {fork[11]==0;fork[11] = 1;}  goto one; 

fi;
one: if
::  d_step {fork[0]==0;fork[0] = 1;}  goto eat; 

fi;
eat: if
:: fork[11] = 0; goto finish; 

fi;
finish: if
:: fork[0] = 0; goto think; 

fi;
}

