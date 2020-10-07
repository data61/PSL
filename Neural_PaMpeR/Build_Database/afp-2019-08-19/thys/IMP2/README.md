# IMP2 --- Simple Program Verification in Isabelle/HOL

IMP2 is a simple imperative language together with Isabelle tooling to 
create a program verification environment in Isabelle/HOL.
The tools include a C-like syntax, a verification condition generator, 
and Isabelle commands for the specification of programs. 
The framework is modular, i.e., it allows easy reuse of already proved programs 
within larger programs.

This entry comes with a quickstart guide and a large collection of examples, 
spanning basic algorithms with simple proofs to more advanced algorithms and 
proof techniques like data refinement.
Some highlights from the examples are: 
  * Bisection Square Root, 
  * Extended Euclid, 
  * Exponentiation by Squaring,
  * Binary Search, 
  * Insertion Sort, 
  * Quicksort,
  * Depth First Search.

The abstract syntax and semantics are very simple and well-documented. 
They are suitable to be used in a course, as extension to the IMP language 
which comes with the Isabelle distribution.

While this entry is limited to a simple imperative language,
the ideas could be extended to more sophisticated languages.


## IMP2 Language Features
  * While-language with recursive procedures
  * Local and global variables, parameter passing via globals 
  * Arrays and integer variables
  * Small-step and big-step semantics
  * Very simple and well-documented abstract syntax and semantics
  
## Tools
  * Verification condition generator
  * Isabelle setup to parse a C-like syntax
  * Isabelle commands to define and prove programs   
  
## Getting Started
  The doc subdirectory contains a quickstart guide and a large collection of example verifications.
  


