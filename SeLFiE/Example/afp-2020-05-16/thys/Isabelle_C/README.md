<div class="source">

``` {.source}
section ‹Isabelle/C›

text ‹
Isabelle/C contains a C99/C11/C18 front-end support for Isabelle. The front-end is actually composed
of two possibly interchangeable parsers (from two different projects):

▪ 🗀‹C11-FrontEnd›: 🌐‹https://hackage.haskell.org/package/language-c›
▪ 🌐‹https://gitlri.lri.fr/ftuong/isabelle_c/tree/C/C18-FrontEnd›:
  🌐‹https://github.com/jhjourdan/C11parser›

At present, the recommended and default version is C11.
›

section ‹Getting started›

text ‹ A first installation step is:
▪ ▩‹isabelle build -D› 🗀‹.›
›
text ‹ which should work out of the box.
›

text ‹ The following C examples or entry-points of documentation can be executed:

▪ ▩‹isabelle jedit -d› 🗀‹.› 🗏‹C11-FrontEnd/examples/C0.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› 🗏‹C11-FrontEnd/examples/C2.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› 🗏‹C11-FrontEnd/examples/C1.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› 🗏‹C11-FrontEnd/C_Appendices.thy›
›

text ‹
▪ The example 🗏‹C11-FrontEnd/examples/C0.thy› is basically used to
demonstrate the faithfulness of the C11 parser implementation.
▪ The example 🗏‹C11-FrontEnd/examples/C2.thy› shows common cases of C and
C editing support in PIDE; it also contains annotation commands without any semantics.
▪ The example 🗏‹C11-FrontEnd/examples/C1.thy› is a show-case for markup
generation and the use of bindings resulting from the static C environment.
▪ The example 🗏‹C11-FrontEnd/C_Appendices.thy› shows the use of
Isabelle/C documentation facilities.
›

text ‹
The AFP version of Isabelle/C does not include semantic back-ends (these are distributed by other
AFP submissions or available via the web; see below). The structure of 🗀‹.› has
been designed to create a directory ‹C11-BackEnds› into which back-ends can be
installed. The structure of 🗀‹.› is actually similar as
🌐‹https://gitlri.lri.fr/ftuong/isabelle_c›: see for example
🌐‹https://gitlri.lri.fr/ftuong/isabelle_c/tree/C/C11-BackEnds› where several
back-ends can be copied and tried.
›

subsection ‹Isabelle/C/README›

text ‹
🗏‹README.md› is automatically generated from 🗏‹README.thy›
using 🌐‹https://gitlri.lri.fr/ftuong/isabelle_c/blob/C/README.sh›.
›

text ‹ Note that this shell-script requires the prior installation of
▩‹pandoc› (🌐‹https://github.com/jgm/pandoc›).
›

section ‹Authors›

text ‹
▪ Frédéric Tuong (🌐‹https://www.lri.fr/~ftuong›)
▪ Burkhart Wolff (🌐‹https://www.lri.fr/~wolff›)
›

section ‹License›

text ‹
Isabelle/C is licensed under a 3-clause BSD-style license (where certain files are in the HPND
license compatible with the 3-clause BSD).

In more details:
▪ The generated files 🗏‹C11-FrontEnd/generated/c_ast.ML› and
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm› are mixing several source code of
    different projects:
  ▪ In 3-clause BSD: the part representing the Haskell Language.C library.  
  ▪ In 2-clause BSD: the C99 AST in HOL (before reflection to SML) adapted from the original
    one in the L4.verified project.
  ▪ In 3-clause BSD: the HOL translation C11 to C99 from the Securify project.    
  ▪ In 3-clause BSD: any other binding and translations of meta-models from the Citadelle
    project.
▪ In 3-clause BSD: the two combined generators generating
  🗏‹C11-FrontEnd/generated/c_ast.ML› based on some modified version of Haskabelle
  and Citadelle.
▪ In 3-clause BSD: the Happy modified generator generating
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm›
▪ In HPND: the ML-Yacc modified generator generating the two
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm.sig› and
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm.sml› (i.e., the ML-Yacc version of
  MLton).
▪ In HPND: the modified grammar library of ML-Yacc loaded in
  🗏‹C11-FrontEnd/src/C_Parser_Language.thy›.
▪ In 3-clause BSD: the remaining files in 🗀‹C11-FrontEnd/src› constituting
  Isabelle/C core implementation.
▪ Most examples in 🗀‹C11-FrontEnd/examples› are in 3-clause BSD, some are
  used for quotation purposes to test the Isabelle/C lexer (hyperlinks around each example detail
  their provenance).
›
```

</div>
