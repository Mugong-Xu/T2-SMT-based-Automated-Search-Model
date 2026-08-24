# Script index

This index distinguishes reusable model/TD modules from executable searches and benchmark variants.  The authoritative parameters remain those in each script.

## GFS-4F

- `smt_model_distinguish.py`: shared cvc5 graph model and symbolic propagation rules.
- `td_trunc.py`: truncated-differential symbol engine and its small demonstration entry point.
- `smt_run_GFS4F_10r.py`: full 10-round, eight-wire SMT trace.
- `smt_run_GFS4F_10r_bench.py`: 100-run benchmark of the full SMT construction.
- `td2smt_GFS4F_from_r4_sliced.py`: TD through Round 4 followed by a relaxed SMT suffix with exact seeding.
- `td2smt_GFS4F_from_r4_sliced_subset.py`: no-tail SMT suffix with subset mask seeding.
- `td2smt_GFS4F_r0to10_assert_r4_bench.py`: full graph with Round-4 TD-derived assertions, benchmarked 100 times.
- `td2smt_GFS4F_r0to10_assert_r4_subst_v2.py`: Round-4 substitution variant and complete suffix trace.

## NEW_II

- `smt_model_distinguish.py`: shared cvc5 graph model.
- `td_trunc.py`: TD propagation engine and demo.
- `search_newstruct6_qd.py`: direct six-round SMT search and Round-6 report.
- `verify_newstruct6_with_smt.py`: TD simulation, safe-anchor selection, and SMT verification.
- `bench_newstruct6_qd.py`: 100-run direct-SMT benchmark.
- `bench_verify_newstruct6.py`: 100-run TD-anchor verification benchmark.

## NEW_III

- `smt_model_distinguish.py`: shared cvc5 graph model.
- `td_trunc.py`: TD propagation engine and demo.
- `smt_12r_new_structure_III_qcpa.py`: direct 12-round SMT search.
- `bencmark_smt_12r_new_structure_III_qcpa.py`: benchmark for the 12-round search (historical filename retained).
- `smt_14r_new_structure_III_qcpa.py`: descending forward-round search, trace export, and decrypt-prune analysis.
- `td_14r_newstruct_III_qcpa.py`: TD-only forward and backward-pruning experiment.
- `bench_14r_newstruct_III_qcpa.py`: repeated TD/pruning benchmark.
- `bench_newstructIII_qd.py`: repeated SMT and decrypt-prune benchmark.
- `bench_newstructIII_qd_from_td.py`: TD-derived anchor followed by an SMT suffix.
- `bench_newstructIII_qd_from_td_sliced.py`: sliced TD-anchor alternative.
- `bench_newstructIII_qd_td_growing.py`: growing-anchor alternative; the bundled configuration is UNSAT and is reported as such.
- `forward_rounds_symbols_13.csv`: exported per-round symbolic states for the selected 13-round run.

## NEW_IV

- `smt_model_distinguish_new_IV.py`: cvc5 graph model adapted for NEW_IV.
- `td_trunc_New_IV.py`: compact TD demonstration for NEW_IV.
- `td_trunc_new.py`, `td_trunc_opt.py`: supporting TD propagation alternatives.
- `smt_run_new_structure_IV_9r.py`: nine-round SMT trace.
- `smt_run_new_structure_IV_11r.py`: 11-round SMT trace.
- `smt_bench_new_structure_IV_11r.py`: repeated 11-round SMT benchmark.
- `td_td2smt_run_New_IV.py`: TD-to-SMT combined run.
- `td_smt_benchmark_New_IV.py`: 100-run combined benchmark.

## NEW_IV_ENC

- `smt_model_distinguish.py`: shared cvc5 graph model.
- `td_trunc.py`: shared TD propagation engine and demo.
- `smt_5r_New_IV.py`: five-round SMT trace.
- `bench_smt_5r_New_IV.py`: repeated five-round SMT benchmark.
- `smt_8r_New_IV.py`: eight-round trace with direct final-round and backward-pruning checks.
- `bench_smt_8r_New_IV.py`: repeated eight-round pruning-based benchmark.
- `td_8r_New_IV.py`: TD-only eight-round trace and pruning result.
- `bench_td_8r_New_IV.py`: 100-run TD-only benchmark.

## Type-1 GFS

- `smt_model_distinguish.py`: strict cvc5 graph model.
- `smt_model_distinguish_relaxed.py`: relaxed model used by selected seeded suffix experiments.
- `td_trunc.py`: TD propagation engine and demo.
- `smt_run_Type1GFS_15r.py`: base 15-round SMT trace.
- `smt_run_Type1GFS_15r_Rrule_xRdelta_to_0s.py`: alternative R-rule constraint variant.
- `smt_run_Type1GFS_15r_strictRsingle.py`: strict single-R variant.
- `smt_run_Type1GFS_15r_relaxed.py`, `smt_run_Type1GFS_15r_relaxed2.py`: relaxed alternatives.
- `sweep_Type1GFS_15r_round12.py`: eight-configuration sweep for a specific Round-12 target mask.
- `sweep_Type1GFS_15r_round12_u1_has_0s.py`: eight-configuration sweep for any `0s` component on `u1^12`.
- `td_run_GFS4F_td_only_10r.py`: retained historical TD-only runner (filename preserved).
- `td_then_smt_Type1GFS_from_r5.py`: strict fixed-seed Round-5-to-15 suffix.
- `td_then_smt_Type1GFS_from_r5_fix.py`: pre-existing corrected-input-name variant.
- `td_then_smt_Type1GFS_from_r5_noinit.py`: suffix variant without the model's initial constraints.
- `td_then_smt_Type1GFS_from_r5_noinit_bench.py`: repeated no-initial-constraint benchmark.
- `td_then_smt_Type1GFS_from_r5_relaxed_bench.py`: repeated relaxed-model suffix benchmark.
- `td_then_smt_Type1GFS_full_15r.py`: TD prefix plus fixed Round-5 seed and relaxed SMT suffix, repeated 100 times.
