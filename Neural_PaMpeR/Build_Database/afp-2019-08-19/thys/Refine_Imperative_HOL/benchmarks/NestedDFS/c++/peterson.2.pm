#define wait0 (P_0@wait)
#define cs0 (P_0@CS)
#define ncs0 (P_0@NCS)
byte pos[3];
byte step[3];


active proctype P_0() { 
byte j=0;
byte k=0;

NCS: if
:: j = 1; goto wait; 

fi;
CS: if
:: pos[0] = 0; goto NCS; 

fi;
wait: if
::  d_step {j<3;pos[0] = j;}  goto q2; 

:: j==3; goto CS; 

fi;
q2: if
::  d_step {step[j-1] = 0;k = 0;}  goto q3; 

fi;
q3: if
::  d_step {k<3 && (k==0 || pos[k]<=j);k = k+1;}  goto q3; 

::  d_step {step[j-1]!=0 || k==3;j = j+1;}  goto wait; 

fi;
}

active proctype P_1() { 
byte j=0;
byte k=0;

NCS: if
:: j = 1; goto wait; 

fi;
CS: if
:: pos[1] = 0; goto NCS; 

fi;
wait: if
::  d_step {j<3;pos[1] = j;}  goto q2; 

:: j==3; goto CS; 

fi;
q2: if
::  d_step {step[j-1] = 1;k = 0;}  goto q3; 

fi;
q3: if
::  d_step {k<3 && (k==1 || pos[k]<=j);k = k+1;}  goto q3; 

::  d_step {step[j-1]!=1 || k==3;j = j+1;}  goto wait; 

fi;
}

active proctype P_2() { 
byte j=0;
byte k=0;

NCS: if
:: j = 1; goto wait; 

fi;
CS: if
:: pos[2] = 0; goto NCS; 

fi;
wait: if
::  d_step {j<3;pos[2] = j;}  goto q2; 

:: j==3; goto CS; 

fi;
q2: if
::  d_step {step[j-1] = 2;k = 0;}  goto q3; 

fi;
q3: if
::  d_step {k<3 && (k==2 || pos[k]<=j);k = k+1;}  goto q3; 

::  d_step {step[j-1]!=2 || k==3;j = j+1;}  goto wait; 

fi;
}

