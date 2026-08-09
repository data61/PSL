Golden fixtures (byte-compared by Contract_Test.thy - a mismatch fails the build):
  verdict_vocabulary.txt, artifact_names.txt, refutation_phrases.txt,
  partial_block.fixture.thy, refutation_record_*.fixture.txt,
  preprocessing_snapshot_header.fixture.txt

Sample fixtures (real captured emissions, NOT byte-compared - they carry run-specific
lemma ids; vendored by consumers as parser-test inputs):
  sample_progress_preprocessing.thy   a mid-search preprocessing-phase snapshot (lemma blocks)
  sample_progress_graph.thy           a graph-phase snapshot (pre-wrapper era shape kept for
                                      classifier robustness; current shape = partial_block)
  sample_final_suggestion_proved.thy  a PROVED search's suggestion (prop_02, the specimen goal)

To change the contract deliberately: delete the golden fixture, rebuild Contract_Test to
regenerate, commit the diff, coordinate with consumers (guide section 5).
