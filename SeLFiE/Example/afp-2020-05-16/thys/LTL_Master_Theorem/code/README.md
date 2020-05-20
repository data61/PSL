# A Verified, Compositional, and Unified Translation of LTL into \<omega>-Automata

The following additional software is required:

- MLton (http://mlton.org/)
- Spot (https://spot.lrde.epita.fr/)
- dot (https://graphviz.org/)

In order to export the code from this theory, execute the following command:

    ./bin/isabelle build -e LTL_Master_Theorem_Constructions

The resulting tool is compiled with the build script that can be found in the tool folder:

    ./build_mlton.sh

The resulting executable can be called as follows, using `autfilt` from Spot and `dot` from graphviz:

    ./ltl_to_dra "F G a" | autfilt --dot=Bar --merge-transitions | dot -Tpdf -O

Our tool can be used as a reference implementation for other, unverified LTL translators.
For example, the following command compares our tool with `ltl2tgba` from Spot:

    randltl -n 3 a b | ltlcross -D "ltl2tgba -s %s >%O" "./ltl_to_dra %s > %O"
