 Title:      PSL/LiFtEr/assertion.md
 Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

MiLkMaId: Machine Learning Mathematical Induction for Isabelle/HOL, and
LiFtEr:   Logical Feature Extractor.
This file contains a list of assertions that 
- a) would be useful to distill the essence of induct methods,
- b) but are very difficult to implement without LiFtEr.

# assertions to judge induction variables regardless of `arbitrary` or `rule`.

## number of arguments
- check if
   - the `induct` method has at least one induction variable

## location with regards to pattern matching of ancestoral nodes.
### patterns (Var excludes the cases the variable appears as part of if-then-else condition or case distinction on the right-hand side.)
| each     |Con|Var|If |Cas|
| :-------:|:-:|:-:|:-:|:-:|
| const    | v |   |   |   |
| just-var |   | v |   |   |
| if       |   |   | v |   | 
| case     |   |   |   | v |

### `foo` - `foo_occ` - `ind_var` - `ind_var_occ` - pattern (64 = 2 x 2 x 2 x 2 x 4)
#### any `foo` - any `foo_occ` - any `ind_var` - any `ind_var_occ` - pattern
- (any `foo` - any `foo_occ` - any `ind_var` - any `ind_var_occ` - Constant) check if
   - for any recursively defined function `foo`,
      - for any occurrence, `foo_occ`, of `foo`,
         - for any induction variable, `ind_var`,
            - for any occurrence, `ind_var_occ`, of `ind_var`,
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`, and
               - a constant is used at the _n_th parameter of `foo` in the definition of `foo`.
- (any `foo` - any `foo_occ` - any `ind_var` - any `ind_var_occ` - Variable) check if
   - for any recursively defined function `foo`,
      - for any occurrence, `foo_occ`, of `foo`,
         - for any induction variable, `ind_var`,
            - for any occurrence, `ind_var_occ`, of `ind_var`,
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`, and
               - a variable is used at the _n_th parameter of `foo` in the definition of `foo`.
- (any `foo` - any `foo_occ` - any `ind_var` - any `ind_var_occ` - IfThenElse) check if
   - for any recursively defined function `foo`,
      - for any occurrence, `foo_occ`, of `foo`,
         - for any induction variable, `ind_var`,
            - for any occurrence, `ind_var_occ`, of `ind_var`,
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`,
               - a variable `var` is used at the _n_th parameter of `foo` in the definition of `foo`, and
               - `var` appears as part of if-then-else condition in the definition of `foo`.
- (any `foo` - any `foo_occ` - any `ind_var` - any `ind_var_occ` - Case) check if
   - for any recursively defined function `foo`,
      - for any occurrence, `foo_occ`, of `foo`,
         - for any induction variable, `ind_var`,
            - for any occurrence, `ind_var_occ`, of `ind_var`,               
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`,
               - a variable `var` is used at the _n_th parameter of `foo` in the definition of `foo`, and
               - `var` appears as part of case distinction in the definition of `foo`.
#### TODO: any `foo` - any `foo_occ` - any `ind_var` - some `ind_var_occ` - pattern
#### TODO: any `foo` - any `foo_occ` - some `ind_var` - any `ind_var_occ` - pattern
#### TODO: any `foo` - any `foo_occ` - some `ind_var` - some `ind_var_occ` - pattern

#### TODO: any `foo` - some `foo_occ` - any `ind_var` - any `ind_var_occ` - pattern
#### TODO: any `foo` - some `foo_occ` - any `ind_var` - some `ind_var_occ` - pattern
#### TODO: any `foo` - some `foo_occ` - some `ind_var` - any `ind_var_occ` - pattern
#### TODO: any `foo` - some `foo_occ` - some `ind_var` - some `ind_var_occ` - pattern

#### TODO: some `foo` - any `foo_occ` - any `ind_var` - any `ind_var_occ` - pattern
#### TODO: some `foo` - any `foo_occ` - any `ind_var` - some `ind_var_occ` - pattern
#### TODO: some `foo` - any `foo_occ` - some `ind_var` - any `ind_var_occ` - pattern
#### TODO: some `foo` - any `foo_occ` - some `ind_var` - some `ind_var_occ` - pattern

#### TODO: some `foo` - some `foo_occ` - any `ind_var` - any `ind_var_occ` - pattern
#### TODO: some `foo` - some `foo_occ` - any `ind_var` - some `ind_var_occ` - pattern
#### TODO: some `foo` - some `foo_occ` - some `ind_var` - any `ind_var_occ` - pattern
#### TODO: some `foo` - some `foo_occ` - some `ind_var` - some `ind_var_occ` - pattern

### `ind_var` - `ind_var_occ` - `foo` - `foo_occ` - pattern (64 = 2 x 2 x 2 x 2 x 4)
#### any `ind_var` - any `ind_var_occ` - any `foo` - any `foo_occ` - pattern
- (any `ind_var` - any `indv_var_occ` - any `foo` - any `foo_occ` - Constant) check if 
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - for any recursively defined function `foo`,
            - for any occurrence, `foo_occ`, of `foo`,
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`, and
               - a constant is used at the _n_th parameter of `foo` in the definition of `foo`.
- (any `ind_var` - any `indv_var_occ` - any `foo` - any `foo_occ` - Variable) check if 
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - for any recursively defined function `foo`,
            - for any occurrence, `foo_occ`, of `foo`,
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`, and
               - a variable is used at the _n_th parameter of `foo` in the definition of `foo`.
- (any `ind_var` - any `indv_var_occ` - any `foo` - any `foo_occ` - IfThenElse) check if 
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - for any recursively defined function `foo`,
            - for any occurrence, `foo_occ`, of `foo`,
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`,
               - a variable `var` is used at the _n_th parameter of `foo` in the definition of `foo`, and
               - `var` appears as part of if-then-else condition in the definition of `foo`.
- (any `ind_var` - any `indv_var_occ` - any `foo` - any `foo_occ` - Case) check if 
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - for any recursively defined function `foo`,
            - for any occurrence, `foo_occ`, of `foo`,
               - `ind_var_occ` appears as part of _n_th argument of `foo_occ`,
               - a variable `var` is used at the _n_th parameter of `foo` in the definition of `foo`, and
               - `var` appears as part of case distinction in the definition of `foo`.
- TODO: any `ind_var` - any `ind_var_occ` - any `foo` - some `foo_occ` - pattern
- TODO: any `ind_var` - any `ind_var_occ` - some `foo` - any `foo_occ` - pattern
- TODO: any `ind_var` - any `ind_var_occ` - some `foo` - some `foo_occ` - pattern

- TODO: any `ind_var` - some `ind_var_occ` - any `foo` - any `foo_occ` - pattern
- TODO: any `ind_var` - some `ind_var_occ` - any `foo` - some `foo_occ` - pattern
- TODO: any `ind_var` - some `ind_var_occ` - some `foo` - any `foo_occ` - pattern
- TODO: any `ind_var` - some `ind_var_occ` - some `foo` - some `foo_occ` - pattern

- TODO: some `ind_var` - any `ind_var_occ` - any `foo` - any `foo_occ` - pattern
- TODO: some `ind_var` - any `ind_var_occ` - any `foo` - some `foo_occ` - pattern
- TODO: some `ind_var` - any `ind_var_occ` - some `foo` - any `foo_occ` - pattern
- TODO: some `ind_var` - any `ind_var_occ` - some `foo` - some `foo_occ` - pattern

- TODO: some `ind_var` - some `ind_var_occ` - any `foo` - any `foo_occ` - pattern
- TODO: some `ind_var` - some `ind_var_occ` - any `foo` - some `foo_occ` - pattern
- TODO: some `ind_var` - some `ind_var_occ` - some `foo` - any `foo_occ` - pattern
- TODO: some `ind_var` - some `ind_var_occ` - some `foo` - some `foo_occ` - pattern
   
## location with regards to (first subgoal / chained facts, premise / coclusion)
### in terms of meta-implication: any `ind_var` - some `ind_var_occ`
- (first subgoal) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the first subgoal.
- (chained facts) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in one of the chained facts.
- (conclusion, first subgoal) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the conclusion of `meta_imp_occ` in the first subgoal.
- (premise, first subgoal) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the premise of `meta_imp_occ` in the first subgoal.
- (conclusion, chained facts) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the conclusion of `meta_imp_occ` in one of the chained facts.
- (premise, chained facts) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the premise of `meta_imp_occ` in one of the chained facts.
            
### in terms of meta-implication: any `ind_var` - any `ind_var_occ`
- (first subgoal) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - `ind_var_occ` appears in the first subgoal.
- (chained facts) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - `ind_var_occ` appears in one of the chained facts.
- (conclusion, first subgoal) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the conclusion of `meta_imp_occ` in the first subgoal.
- (premise, first subgoal) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the premise of `meta_imp_occ` in the first subgoal.
- (conclusion, chained facts) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the conclusion of `meta_imp_occ` in one of the chained facts.
- (premise, chained facts) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `ind_var_occ` appears in the premise of `meta_imp_occ` in one of the chained facts.
            
## location with regards to depth
### in terms of depth of a function:
- (any `ind_var` - any `ind_var_occ` - some `ptrm` - some `foo`) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists a PROP term, `ptrm`, such that
            - there exists a function, `foo`, such that
               - `ind_var_occ` appears as part of an argument `foo`, and
               - `ind_var_occ` is the deepest function application in `ptrm`.
- (any `ind_var` - some `ind_var_occ` - some `ptrm` - some `foo`) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists a PROP term, `ptrm`, such that
            - there exists a function, `foo`, such that
               - `ind_var_occ` appears as part of an argument `foo`, and
               - `ind_var_occ` is the deepest function application in `ptrm`.
- (some `ind_var` - any `ind_var_occ` - some `ptrm` - some `foo`) check if
   - there exists an induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists a PROP term, `ptrm`, such that
            - there exists a function, `foo`, such that
               - `ind_var_occ` appears as part of an argument `foo`, and
               - `ind_var_occ` is the deepest function application in `ptrm`.
- (some `ind_var` - some `ind_var_occ` - some `ptrm` - some `foo`) check if
   - there exists an induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists a PROP term, `ptrm`, such that
            - there exists a function, `foo`, such that
               - `ind_var_occ` appears as part of an argument `foo`, and
               - `ind_var_occ` is the deepest function application in `ptrm`.

### in terms of depth of an induction variable:
- (any `ind_var` - any `ind_var_occ` - some `ptrm`) check if
   - for any induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists a PROP term, `ptrm`, such that
            - `ind_var_occ` is at the lowest level in `ptrm`.
- (any `ind_var` - some `ind_var_occ` - some `ptrm`) check if
   - for any induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists a PROP term, `ptrm`, such that
            - `ind_var_occ` is at the lowest level in `ptrm`.
- (some `ind_var` - any `ind_var_occ` - some `ptrm`) check if
   - there exists an induction variable, `ind_var`,
      - for any occurrence, `ind_var_occ`, of `ind_var`,
         - there exists a PROP term, `ptrm`, such that
            - `ind_var_occ` is at the lowest level in `ptrm`.
- (some `ind_var` - some `ind_var_occ` - some `ptrm`) check if
   - there exists an induction variable, `ind_var`,
      - there exists an occurrence, `ind_var_occ`, of `ind_var`, such that
         - there exists a PROP term, `ptrm`, such that
            - `ind_var_occ` is at the lowest level in `ptrm`.

# assertions to judge `rule` regardless of induction variables or `arbitrary`.
- check if
   - the `induct` method has at least one `rule` argument
   
## location
### with regards to (first subgoal / chained facts, premise / coclusion) (one `const.induct` - some `const_occ` - location)
- (first subgoal) check if
   - there exists exactly one argument, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - `const_occ` appears in the first subgoal.
- (chained facts) check if
   - there exists exactly one argument, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - `const_occ` appears in one of the chained facts.
- (conclusion, first subgoal) check if
   - there exists exactly one argument, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `const_occ` appears in the conclusion of `meta_imp_occ` in the first subgoal.
- (premise, first subgoal) check if
   - there exists exactly one argument, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `const_occ` appears in the premise of `meta_imp_occ` in the first subgoal.
- (conclusion, chained facts) check if
   - there exists exactly one argument, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `const_occ` appears in the conclusion of `meta_imp_occ` in one of the chained facts.
- (premise, chained facts) check if
   - there exists exactly one argument, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - there exists an occurrence, `meta_imp_occ` of the meta-implication, such that
            - `const_occ` appears in the premise of `meta_imp_occ` in one of the chained facts.

# assertions to judge induction variables and `arbitrary`.
- check if
   - the `induct` method has at least one `arbitrary` argument
- TODO: multiple recursively defined ancestors shared with induction variables. (the same function or not, for (any / some) generalized variable, for (any / some) induction variables, for (any / some) recursively defined).
## `arb_var` - `foo` - `ind_var`
- (any `arb_var` - some `arb_var_occ` - some `foo` - some `foo_occ1` and `foo_occ2` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`) check if
   - for any generalized variable, `arb_var`,
      - there exists an occurrence, `arb_var_occ`, of `arb_var`, such that
         - there exists a recursively defined function `foo`, such that
            - there exists an occurrence, `foo_occ1`, of `foo`, such that
               - `foo_occ1` is an ancestor of `arb_var_occ`, and
               - there exists an occurrence, `foo_occ2`, of `foo`, such that
                  - `foo_occ1` and `foo_occ2` are different occurrences,
                  - `foo_occ2` is an ancestor of `arb_var_occ`, and
                  - there exists an induction variable `ind_var`, such that
                     - there exists an occurrence of `ind_var_occ1`, such that
                        - `foo_occ1` is an ancestor of `ind_var_occ1`,
                        - `foo_occ2` is an ancestor of `ind_var_occ1`, and
                        - there exists an occurrence of `ind_var_occ2`, such that
                           - `ind_var_occ1` and `ind_var_occ2` are different occurrences,
                           - `foo_occ1` is an ancestor of `ind_var_occ2`, and
                           - `foo_occ2` is an ancestor of `ind_var_occ2`.
                         
- (any `arb_var` - some `arb_var_occ` - some `foo` - some `foo_occ1` and `foo_occ2` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`) check if
   - for any generalized variable, `arb_var`,
      - there exists an occurrence, `arb_var_occ`, of `arb_var`, such that
         - there exists a recursively defined function `foo`, such that
            - there exists an occurrence, `foo_occ1`, of `foo`, such that
               - `foo_occ1` is an ancestor of `arb_var_occ`, and
               - there exists an occurrence, `foo_occ2`, of `foo`, such that
                  - `foo_occ1` and `foo_occ2` are different occurrences,
                  - `foo_occ2` is an ancestor of `arb_var_occ`, and
                  - for any induction variable `ind_var`,
                     - there exists an occurrence of `ind_var_occ1`, such that
                        - `foo_occ1` is an ancestor of `ind_var_occ1`,
                        - `foo_occ2` is an ancestor of `ind_var_occ1`, and
                        - there exists an occurrence of `ind_var_occ2`, such that
                           - `ind_var_occ1` and `ind_var_occ2` are different occurrences,
                           - `foo_occ1` is an ancestor of `ind_var_occ2`, and
                           - `foo_occ2` is an ancestor of `ind_var_occ2`.
                           
- (any `arb_var` - some `arb_var_occ` - some `foo` - any `foo_occ` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`) check if
   - for any generalized variable, `arb_var`,
      - there exists an occurrence, `arb_var_occ`, of `arb_var`, such that
         - there exists a recursively defined function `foo`, such that
            - for any occurrence, `foo_occ`, of `foo`,
               - `foo_occ` is an ancestor of `arb_var_occ`, and
               - there exists an induction variable `ind_var`, such that
                  - there exists an occurrence of `ind_var_occ1`, such that
                     - `foo_occ` is an ancestor of `ind_var_occ1`, and
                     - there exists an occurrence of `ind_var_occ2`, such that
                        - `ind_var_occ1` and `ind_var_occ2` are different occurrences, and
                        - `foo_occ` is an ancestor of `ind_var_occ2`.

- (any `arb_var` - some `arb_var_occ` - some `foo` - any `foo_occ` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`) check if
   - for any generalized variable, `arb_var`,
      - there exists an occurrence, `arb_var_occ`, of `arb_var`, such that
         - there exists a recursively defined function `foo`, such that
            - for any occurrence, `foo_occ`, of `foo`,
               - `foo_occ` is an ancestor of `arb_var_occ`, and
               - for any induction variable `ind_var`,
                  - there exists an occurrence of `ind_var_occ1`, such that
                     - `foo_occ` is an ancestor of `ind_var_occ1`, and
                     - there exists an occurrence of `ind_var_occ2`, such that
                        - `ind_var_occ1` and `ind_var_occ2` are different occurrences, and
                        - `foo_occ` is an ancestor of `ind_var_occ2`.
- (any `arb_var` - some `arb_var_occ` - any `foo` - some `foo_occ1` and `foo_occ2` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`) check if
   - for any generalized variable, `arb_var`,
      - there exists an occurrence, `arb_var_occ`, of `arb_var`, such that
         - for any recursively defined function `foo`,
            - there exists an occurrence, `foo_occ1`, of `foo`, such that
               - `foo_occ1` is an ancestor of `arb_var_occ`, and
               - there exists an occurrence, `foo_occ2`, of `foo`, such that
                  - `foo_occ1` and `foo_occ2` are different occurrences,
                  - `foo_occ2` is an ancestor of `arb_var_occ`, and
                  - there exists an induction variable `ind_var`, such that
                     - there exists an occurrence of `ind_var_occ1`, such that
                        - `foo_occ1` is an ancestor of `ind_var_occ1`,
                        - `foo_occ2` is an ancestor of `ind_var_occ1`, and
                        - there exists an occurrence of `ind_var_occ2`, such that
                           - `ind_var_occ1` and `ind_var_occ2` are different occurrences,
                           - `foo_occ1` is an ancestor of `ind_var_occ2`, and
                           - `foo_occ2` is an ancestor of `ind_var_occ2`.

- TODO: any `arb_var` - some `arb_var_occ` - any `foo` - some `foo_occ1` and `foo_occ2` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - any `foo` - any `foo_occ` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - any `foo` - any `foo_occ` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
## `arb_var` - `foo` and `bar` - `ind_var`
- TODO: any `arb_var` - some `arb_var_occ` - some `foo` and `bar` - some `foo_occ` and `bar_occ` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - some `foo` and `bar` - some `foo_occ` and `bar_occ` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - some `foo` and `bar` - any `foo_occ` and `bar_occ` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - some `foo` and `bar` - any `foo_occ` and `bar_occ` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - any `foo` and `bar` - some `foo_occ` and `bar_occ` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- for any generalized variable, `arb_var`,
   - there exists an occurrence, `arb_var_occ`, of `arb_var`, such that
      - for any recursively defined function `foo`,
         - there exists an occurrence, `foo_occ`, of `foo`, such that
            - `foo_occ` is an ancestor of `arb_var_occ`, and
            - for any recursively defined function `bar`,
               - there exists an occurrence, `bar_occ`, of `bar`, such that
               - `foo_occ` and `bar_occ` are different occurrences,
               - `bar_occ` is an ancestor of `arb_var_occ`, and
               - there exists an induction variable `ind_var`, such that
                  - there exists an occurrence of `ind_var_occ1`, such that
                     - `foo_occ` is an ancestor of `ind_var_occ1`,
                     - `bar_occ` is an ancestor of `ind_var_occ1`, and
                     - there exists an occurrence of `ind_var_occ2`, such that
                        - `ind_var_occ1` and `ind_var_occ2` are different occurrences, and
                           - `foo_occ` is an ancestor of `ind_var_occ2`, and
                           - `bar_occ` is an ancestor of `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - any `foo` and `bar` - some `foo_occ` and `bar_occ` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - any `foo` and `bar` - any `foo_occ` and `bar_occ` - some `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
- TODO: any `arb_var` - some `arb_var_occ` - any `foo` and `bar` - any `foo_occ` and `bar_occ` - any `ind_var` - some `ind_var_occ1` and `ind_var_occ2`.
## `ind_var` - `foo` - `arb_var`
- TODO: some `ind_var` - some `ind_var_occ1` and `ind_var_occ2` - some `foo` - some `foo_occ1` and `foo_occ2` - any `arb_var` - some `arb_var_occ`.
- TODO: any `ind_var` - some `ind_var_occ1` and `ind_var_occ2` - some `foo` - some `foo_occ1` and `foo_occ2` - any `arb_var` - some `arb_var_occ`.
- TODO: some `ind_var` - some `ind_var_occ1` and `ind_var_occ2` - some `foo` - any `foo_occ` - any `arb_var` - some `arb_var_occ`.
- TODO: some `ind_var_occ1` and `ind_var_occ2` - some `foo` - any `foo_occ` - any `ind_var` - any `arb_var` - some `arb_var_occ`.
- TODO: some `ind_var` - some `ind_var_occ1` and `ind_var_occ2` - any `foo` - some `foo_occ1` and `foo_occ2` - any `arb_var` - some `arb_var_occ`.
- TODO: any `ind_var` - some `ind_var_occ1` and `ind_var_occ2` - any `foo` - some `foo_occ1` and `foo_occ2` - any `arb_var` - some `arb_var_occ` .
- TODO: some `ind_var` - some `ind_var_occ1` and `ind_var_occ2` - any `foo` - any `foo_occ` - any `arb_var` - some `arb_var_occ`.
- TODO: any `ind_var` - some `ind_var_occ1` and `ind_var_occ2` - any `foo` - any `foo_occ` - any `arb_var` - some `arb_var_occ`.
## `ind_var` - `foo` and `bar` - `arb_var`
- TODO: any `ind_var` - some `ind_var_occ` - some `foo` and `bar`- some `foo_occ` and `bar_occ` - some `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.
- TODO: any `ind_var` - some `ind_var_occ` - some `foo` and `bar` - some `foo_occ` and `bar_occ` - any `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.
- TODO: any `ind_var` - some `ind_var_occ` - some `foo` and `bar` - any `foo_occ` and `bar_occ` - some `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.
- TODO: any `ind_var` - some `ind_var_occ` - some `foo` and `bar` - any `foo_occ` and `bar_occ` - any `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.
- TODO: any `ind_var` - some `ind_var_occ` - any `foo` and `bar` - some `foo_occ` and `bar_occ` - some `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.
- TODO: any `ind_var` - some `ind_var_occ` - any `foo` and `bar` - some `foo_occ` and `bar_occ` - any `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.
- TODO: any `ind_var` - some `ind_var_occ` - any `foo` and `bar` - any `foo_occ` and `bar_occ` - some `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.
- TODO: any `ind_var` - some `ind_var_occ` - any `foo` and `bar` - any `foo_occ` and `bar_occ` - any `arb_var` - some `arb_var_occ1` and `arb_var_occ2`.

# assertions to judge induction variables and `rule` 
## (`const_occ` - `ind_var` - part)
- (one `const-induct` - some `const_occ` - any `ind_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - for any induction variable, `ind_var`, 
            - `ind_var` appears as part of `const_occ`'s argument.
- (some `const_occ` - any `ind_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - there exists an occurrence, `const_occ`, of `const`, such that
        - for any induction variable, `ind_var`, 
           - `ind_var` appears as ~part of~ `const_occ`'s argument.
- (some `const_occ` - some `ind_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, and
      - there exists an occurrence, `const_occ`, of `const`, such that
         - there exists an induction variable, `ind_var`, 
            - `ind_var` appears as part of `const_occ`'s argument.
- (some `const_occ` - some `ind_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - there exists an occurrence, `const_occ`, of `const`, such that
        - there exists an induction variable, `ind_var`, 
           - `ind_var` appears as ~part of~ `const_occ`'s argument.
- (any `const_occ` - any `ind_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any occurrence, `const_occ`, of `const`,
         - for any induction variable, `ind_var`, 
            - `ind_var` appears as part of `const_occ`'s argument.
- (any `const_occ` - any `ind_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - for any occurrence, `const_occ`, of `const`,
        - for any induction variable, `ind_var`, 
           - `ind_var` appears as ~part of~ `const_occ`'s argument.
- (any `const_occ` - some `ind_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any occurrence, `const_occ`, of `const`,
         - there exists an induction variable, `ind_var`, 
            - `ind_var` appears as part of `const_occ`'s argument.
- (any `const_occ` - some `ind_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - for any occurrence, `const_occ`, of `const`,
        - there exists an induction variable, `ind_var`, 
           - `ind_var` appears as ~part of~ `const_occ`'s argument.

## (`ind_var` - `const_occ` - part)
- (one `const-induct` - any `ind_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `ind_var`, 
         - any occurrence, `const_occ`, of `const`,
            - `ind_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `ind_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `ind_var`, 
         - any occurrence, `const_occ`, of `const`,
            - `ind_var` appears as ~part of~ `const_occ`'s argument.
- (one `const-induct` - any `ind_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `ind_var`, 
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `ind_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `ind_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `ind_var`, 
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `ind_var` appears as ~part of~ `const_occ`'s argument.
- (one `const-induct` - some `ind_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `ind_var`, such that
         - any occurrence, `const_occ`, of `const`,
            - `ind_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `ind_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `ind_var`, such that
         - any occurrence, `const_occ`, of `const`,
            - `ind_var` appears as ~part of~ `const_occ`'s argument.
- (one `const-induct` - any `ind_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `ind_var`, such that
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `ind_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `ind_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `ind_var`, such that
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `ind_var` appears as ~part of~ `const_occ`'s argument.

# assertions to judge `arbitrary` and `rule` 
## (`const_occ` - `arb_var` - part)
- (one `const-induct` - some `const_occ` - any `arb_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an occurrence, `const_occ`, of `const`, such that
         - for any generalized variable, `arb_var`, 
            - `arb_var` appears as part of `const_occ`'s argument.
- (some `const_occ` - any `arb_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - there exists an occurrence, `const_occ`, of `const`, such that
        - for any induction variable, `arb_var`, 
           - `arb_var` appears as ~part of~ `const_occ`'s argument.
- (some `const_occ` - some `arb_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, and
      - there exists an occurrence, `const_occ`, of `const`, such that
         - there exists an induction variable, `arb_var`, 
            - `arb_var` appears as part of `const_occ`'s argument.
- (some `const_occ` - some `arb_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - there exists an occurrence, `const_occ`, of `const`, such that
        - there exists an induction variable, `arb_var`, 
           - `arb_var` appears as ~part of~ `const_occ`'s argument.
- (any `const_occ` - any `arb_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any occurrence, `const_occ`, of `const`,
         - for any induction variable, `arb_var`, 
            - `arb_var` appears as part of `const_occ`'s argument.
- (any `const_occ` - any `arb_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - for any occurrence, `const_occ`, of `const`,
        - for any induction variable, `arb_var`, 
           - `arb_var` appears as ~part of~ `const_occ`'s argument.
- (any `const_occ` - some `arb_var` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any occurrence, `const_occ`, of `const`,
         - there exists an induction variable, `arb_var`, 
            - `arb_var` appears as part of `const_occ`'s argument.
- (any `const_occ` - some `arb_var` - not-just-part) check if
  - there exists exactly one rule, `const.induct`, to the rule field, such that
     - for any occurrence, `const_occ`, of `const`,
        - there exists an induction variable, `arb_var`, 
           - `arb_var` appears as ~part of~ `const_occ`'s argument.

## (`arb_var` - `const_occ` - part)
- (one `const-induct` - any `arb_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `ind_var`, 
         - any occurrence, `const_occ`, of `const`,
            - `arb_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `arb_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `arb_var`, 
         - any occurrence, `const_occ`, of `const`,
            - `arb_var` appears as ~part of~ `const_occ`'s argument.
- (one `const-induct` - any `arb_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `arb_var`, 
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `arb_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `arb_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - for any induction variable, `arb_var`, 
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `arb_var` appears as ~part of~ `const_occ`'s argument.
- (one `const-induct` - some `arb_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `arb_var`, such that
         - any occurrence, `const_occ`, of `const`,
            - `arb_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `arb_var` - any `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `arb_var`, such that
         - any occurrence, `const_occ`, of `const`,
            - `arb_var` appears as ~part of~ `const_occ`'s argument.
- (one `const-induct` - any `arb_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `arb_var`, such that
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `arb_var` appears as part of `const_occ`'s argument.
- (one `const-induct` - any `arb_var` - some `const_occ` - part) check if
   - there exists exactly one rule, `const.induct`, to the rule field, such that
      - there exists an induction variable, `arb_var`, such that
         - there exists an occurrence, `const_occ`, of `const`, such that
            - `arb_var` appears as ~part of~ `const_occ`'s argument.
            
# constants defined in the standard library
- TODO

# other assertions
- TODO