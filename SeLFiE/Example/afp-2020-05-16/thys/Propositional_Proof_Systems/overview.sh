#!/bin/bash

set -e -u

IV="${IV:-feh}"
act="${1:-view}"
typ="${2:-all}"

(
cat <<<'
	digraph theories {
		graph [
			rankdir = BT;
			overlap=scalexy;
			//nodesep=0.6;
			dpi = 300;
		];
		node [
			fontname = "Helvetica";
			fontsize=16;
		];
		edge [
		//	weight=0.2
			style="-stealth,very thin"
		];
		Formulas [label="Formula Syntax"];
		Sema [label="Semantics"];
		SC [label="Sequent Calculus"];
		SC_Cut [label="SC: cut\ncontraction"];
		SC_Gentzen [label="Gentzen Style SC"];
		SC_Compl_Consistency [label="SC complete\n(via Consistency)"];
		SC_Depth [label="SC derivations\nand depth"];
		SC_Depth_Limit [label="SC derivations and\na limit for depth"];
		MiniFormulas [label="→ only formulas"];
		MiniFormulas_Sema [label="proof that\n→ transformation\nis sound"];
		MiniSC_Craig [label="Interpolation using SC"];
		Sema_Craig [label="Interpolation\nusing Semantics"];
		HC [label="Hilbert Calculus"];
		HC_Compl_Consistency [label="HC complete\n(via consistency)"];
		ND [label="Natural Deduction"];
		SCND [label="SC→ND"];
		NDHC [label="ND→HC"];
		HCSC [label="HC→SC"];
		HCSCND [label="Single Formula\nprovability equivalence\nHC↔ND↔SC"];
		SC_Sema [label="SC sound/complete"];
		ND_Sound [label="ND soundness"];
		ND_Compl_SC [label="ND completeness\n(via SC)"];
		ND_Compl_Truthtable [label="ND completeness\n(simulates truthtables)"];
		ND_Compl_Truthtable_Compact [label="ND completeness\n(generalized)"];
		MiniSC_HC [label="→ only: SC→HC"];
		MiniSC [label="→ only transformation:\nSC invariant"];
		ND_FiniteAssms [label="ND and a dead end\nto compactness"];
		Resolution [label="Resolution"];
		LSC_Resolution [label="LSC ↔ Resolution"];
		Resolution_Compl_SC_Small [label="Resolution completeness via LSC\n(using semantic correctness of formula CNF trans.)"];
		Resolution_Compl_SC_Full [label="Resolution completeness\nvia LSC"];
		Resolution_Compl_Consistency [label="Resolution complete\n(via Consistency)"];
		Resolution_Compl [label="Resolution completeness\n(induction over atom set)"];
		Resolution_Sound [label="Resolution soundness"];
		LSC [label="Transforming SC: to CNF,\nto left handed SC (LSC)"];
		Substitution [label="Substitutions"];
		Substitution_Sema [label="Substitution lemma"];
		Compactness_Consistency [label="Compactness\n(via Consistency)"];
		Consistency [label="Abstract Consistency\nProperties"];
		Tseytin [label="Tseytin transformation"];
		Tseytin_Sema [label="Tseytin transformation:\ncorrectness"];
		CNF [label="CNFs"];
		CNF_Sema [label="Semantics of CNFs"];
		CNF_Formulas [label="Formulas in CNF"];
		CNF_Formulas_Sema [label="Formulas→CNF:\ncorrectness"];
		CNF_To_Formula [label="Converting CNFs\nback to formulas"];
	'

for f in *.thy; do
	sed -n '/imports/ { :nl; /begin/ ! {N;b nl}; s/imports//; s/begin//; s/ /\n/g; s/"[^\n]*//g; s/\n\n/\n/g; s/^\n*//; s/\n*$//; p };' "$f" |\
	while read i; do echo "${f/.thy/} -> $i;"; done;
done

echo '}'

) | \
if [[ "$typ" == "prooftran" ]]; then
	grep -ve "Sema\|ROBDD\|Compactness\|Consisten\|Compl\|Sound\|Substitution\|Tseytin\|CNF_To_Formula\|Main"
elif [[ "$typ" == "sema" ]]; then
	sed -n '/->\|label=/ ! p; /\(.*Sema.*\|.*Sound.*\|.*Compl.*\|SC\|ROBDD\|Compactness\|SC_Depth.*\|Substitution\|Tseytin.*\|HC\|.*Consisten.*\|SC_Cut\|LSC.*\|CNF.*\|Resolution.*\|.*Formula.*\|\(^\|\W\)ND\|\(^\|\W\)SC\|SCc\|SCND\) \(\[\|->\)/ {/Main\|HCSCND\|SingleForm\|MiniSC\|NDHC\|HCSC/ ! p}'
elif [[ "$typ" == "all" ]]; then
	grep -ve "Main"
else
	(>&2 echo "unknown type")
fi | \
if [[ "$act" == "view" ]]; then
	dot -Tpng | $IV -
elif [[ "$act" == "dump" ]]; then
	cat
elif [[ "$act" == "tex" ]]; then
	dot -Txdot | dot2tex --figonly --graphstyle='scale=0.15, every node/.style={scale=0.3}'
else
	(>&2 echo "unknown action")
fi
