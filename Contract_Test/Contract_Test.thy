(*  Title:      Contract_Test/Contract_Test.thy

The producer's half of the PSL/consumer contract, enforced.

External consumers - first among them the Heinzelmen webservice - parse what this prover
emits: the verdict vocabulary, the artifact names beside verdicts.csv, the two phrases that
anchor counterexample extraction, the pasteable partial block, the refutation record's line
format, and the preprocessing snapshot's header. A change to any of these is invisible to our
own build and breaks theirs weeks later at their next repin - unless it fails HERE, in front
of the person making it.

Golden fixtures: each check renders the contract surface and compares it byte-for-byte
against a committed file under fixtures/. A missing fixture is generated (bootstrap: commit
it); a mismatch fails the build with instructions. Changing the contract deliberately means
deleting the fixture, rebuilding, committing the diff - which makes the change VISIBLE in
review and in every consumer that vendors these fixtures for its own tests.
*)
theory Contract_Test
  imports Smart_Isabelle.Smart_Isabelle
begin

ML \<open>
local

val fixtures_dir =
  Path.append (Resources.master_directory \<^theory>) (Path.basic "fixtures");

fun check msg b = if b then () else error ("Contract_Test: " ^ msg);

fun golden (name: string) (actual: string): unit =
  let
    val path = Path.append fixtures_dir (Path.basic name);
  in
    if File.exists path
    then
      let val expected = File.read path in
        if expected = actual then ()
        else
          error ("Contract_Test: contract surface changed - fixture mismatch for " ^ name
                 ^ ".\nIf this change is intentional: delete " ^ Path.implode path
                 ^ ",\nrebuild to regenerate, commit the diff, and coordinate with consumers\n\
                 \(docs/2026_08_09_partial_proofs_guide.html, section 5).\n\
                 \--- expected ---\n" ^ expected ^ "--- actual ---\n" ^ actual)
      end
    else
      (Isabelle_System.make_directory fixtures_dir;
       File.write path actual;
       writeln ("Contract_Test: generated fixture " ^ name ^ " - commit it"))
  end;

in

(** the verdict vocabulary and artifact names **)

val _ =
  golden "verdict_vocabulary.txt"
    (cat_lines
       [Top_Down_Util.verdict_proved, Top_Down_Util.verdict_unproved,
        Top_Down_Util.verdict_proved_applied, Top_Down_Util.verdict_refuted] ^ "\n");

val _ =
  golden "artifact_names.txt"
    (cat_lines
       [Top_Down_Util.verdicts_file_name,
        "<theory>" ^ Top_Down_Util.progress_file_suffix,
        "<theory>" ^ Top_Down_Util.refutation_file_suffix] ^ "\n");

(** the extraction anchor phrases **)

val _ =
  golden "refutation_phrases.txt"
    (Proof_By_Abduction.refutation_message_prefix ^ "\n"
     ^ Proof_By_Abduction.refutation_trace_prefix ^ "\n");

(** the pasteable partial block **)

val partial_block_sample =
  Proof_By_Abduction.wrap_partial_block
    "have example_prelude_1: \"x nil2 var_1 = var_1\" for var_1\napply auto\ndone"
    "have example_graph_1: \"length (x var_1 var_2) = length (x var_2 var_1)\" for var_2 var_1\napply (auto simp add: example_prelude_1)\ndone";

val _ = golden "partial_block.fixture.thy" (partial_block_sample ^ "\n");

(*Structural guarantees, stated independently of the exact bytes: consumers classify on
  these, so they must survive even a deliberate fixture regeneration.*)
val _ =
  check "the partial block announces failure in its first line"
    (String.isPrefix "(* AbductionProver did not prove the goal" partial_block_sample);
val _ =
  check "the partial block opens a proof"
    (String.isSubstring "\nproof -" partial_block_sample);
val _ =
  check "the partial block closes with show ?thesis sorry / qed"
    (String.isSuffix "show ?thesis sorry\nqed" partial_block_sample);

(** the refutation record's line format **)

val _ =
  golden "refutation_record_quickcheck.fixture.txt"
    (cat_lines
       (Proof_By_Abduction.refutation_report_lines
          {qc_outcome = "genuine", qc_secs = 2.4, np_outcome = "not run: quickcheck refuted",
           np_secs = 0.0, counterexample = SOME "b = 0, a = 1"}) ^ "\n");

val _ =
  golden "refutation_record_nitpick.fixture.txt"
    (cat_lines
       (Proof_By_Abduction.refutation_report_lines
          {qc_outcome = "disabled", qc_secs = 0.0, np_outcome = "genuine", np_secs = 4.5,
           counterexample =
             SOME "Auto Nitpick found a counterexample: Free variable: n = 5"}) ^ "\n");

(** the preprocessing snapshot's header **)

val _ =
  golden "preprocessing_snapshot_header.fixture.txt"
    Proof_By_Abduction.preprocessing_snapshot_header;

val _ =
  check "the preprocessing header names the paste position"
    (String.isSubstring "ABOVE your theorem" Proof_By_Abduction.preprocessing_snapshot_header);

val _ = writeln "Contract_Test: all contract surfaces verified";

end
\<close>

end
