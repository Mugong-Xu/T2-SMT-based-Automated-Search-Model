# T²-SMT-based Automated Search Model

This repository collects six experimental code bases for automated periodic-distinguisher analysis with truncated-differential (TD) propagation and SMT solving.  The code represents each propagated state with a five-bit symbolic mask over

`{δ, R(δ), x, R(x), 0s}`

and uses a separate bottom marker (`⊥`) for an invalid or pruned branch.  The experiments cover GFS-4F, three new four-branch structures, an encryption-oriented NEW_IV variant, and Type-1 GFS.

> **Interpretation note.** `sat` means that the constraints encoded by a particular script are satisfiable.  Likewise, “quantum distinguisher: yes/no” is the result of that script's stated symbolic or backward-pruning criterion; it is not, by itself, an independent security proof.

## Repository layout

| Path | Contents |
|---|---|
| `GFS-4F/` | 10-round, eight-wire GFS-4F SMT, TD→SMT, sliced, substitution, and benchmark experiments |
| `NEW_II/` | Six-round NEW_II search and TD-anchored SMT verification |
| `NEW_III/` | 12/13-round forward models, TD/SMT anchor variants, decrypt-prune checks, and benchmarks |
| `NEW_IV/` | 9/11-round NEW_IV SMT and TD→SMT experiments |
| `NEW_IV_ENC/` | Five- and eight-round encryption-oriented NEW_IV experiments with backward pruning |
| `Type-1 GFS/` | 15-round Type-1 GFS strict/relaxed models, parameter sweeps, and TD→SMT variants |
| `scripts/run_all.py` | Discovers and runs every Python file with a `__main__` entry point |
| `results/SUMMARY.md` | Machine-readable run status rendered as a Markdown table |
| `results/summary.csv` | Project, script, exit status, duration, and raw-log path for all runs |
| `results/raw/` | Captured stdout and stderr for every experiment |
| `docs/SCRIPT_INDEX.md` | File-by-file guide to the experimental variants |

The source directory names and historical filenames (including `bencmark_...`) are preserved so that existing references remain valid.  Python caches and Windows `Zone.Identifier` metadata are intentionally excluded.

## Reproduce the results

The committed run was produced in WSL2 with Ubuntu 22.04, Python 3.10.12, and cvc5 1.3.0.

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -r requirements.txt
python scripts/run_all.py --timeout 120
```

The runner executes each script from its own project directory, disables bytecode generation, captures stdout/stderr, and regenerates `results/summary.csv` and `results/SUMMARY.md`.  A nonzero runner exit code means at least one experiment failed or timed out.  To run an individual experiment, invoke it from its directory, for example:

```bash
cd NEW_II
python search_newstruct6_qd.py
```

## Results from the bundled run

All **50/50 executable scripts completed successfully**; none timed out.  Representative outcomes are below.  Times are wall-clock measurements on one WSL2 host and should be treated as indicative rather than portable performance claims.

| Project / experiment | Observed outcome | Representative timing |
|---|---|---:|
| GFS-4F, 10-round full SMT | SAT; Round 10 leaves `u0 = R(δ) ⊕ 0s`, with the other seven branches at `⊥` | 191.767 ms/run over 100 runs for the Round-4-asserted benchmark |
| GFS-4F, sliced TD→SMT | The strict and subset-seeded suffix variants are UNSAT; the Round-4 substitution variant is SAT | See raw logs |
| NEW_II, six rounds | SAT; the script reports a distinguisher and Round 6 leaves `U2 = R(δ) ⊕ 0s` | TD-anchor verification: 25.730 ms/run, 100/100 SAT |
| NEW_III, forward + decrypt-prune | A 13-round forward instance is SAT; backward pruning terminates at `u1^10 = 0s` | TD-anchor hybrid: 57.675 ms/run over 100 runs |
| NEW_III, growing TD anchor | SMT suffix is UNSAT, so this variant reports no distinguisher | 5.725 ms/run over 100 runs |
| NEW_IV, 11 rounds | SAT; Round 11 leaves only `u3 = 0s ⊕ R(x) ⊕ x ⊕ R(δ)` | 14.380 ms/run over 100 runs |
| NEW_IV_ENC, eight rounds | Forward SMT is SAT but all Round-8 outputs are `⊥`, so the direct final-round test says “no”; backward pruning instead reaches `u3^4 = 0s` and the pruning-based benchmark says “yes” | SMT/pruning: 28.496 ms/run; TD-only: 0.036 ms/run |
| Type-1 GFS, 15 rounds | Base model is SAT but all Round-15 branches are `⊥`; strict-R variants are UNSAT.  The relaxed, fixed Round-5-seed benchmark is SAT | Relaxed TD→SMT: 2.167 ms/run over 100 runs |
| Type-1 GFS, Round-12 sweeps | None of the tested configurations produces the requested `u1^12` target or any `0s` bit | 8 configurations per sweep |

For exact models, complete round traces, and stderr, use [results/SUMMARY.md](results/SUMMARY.md) and follow its links to the raw logs.

## Compatibility corrections in this organized copy

The original directories under `/home/xys/proj` were not modified.  Three minimal runtime corrections were applied only to this repository copy after the first complete run exposed them:

1. `GFS-4F/td2smt_GFS4F_from_r4_sliced_subset.py` now passes `tails=[]` explicitly.  This preserves its intended no-tail experiment while satisfying the current `build_from_graph` schema.
2. `NEW_III/bench_newstructIII_qd_td_growing.py` now records an UNSAT result without calling cvc5 `getValue()` when no model exists.
3. `Type-1 GFS/td_then_smt_Type1GFS_from_r5.py` now uses the model API's input identifiers (`u0_0` through `u0_3`), matching the already-present `_fix` variant.

These changes repair execution and result reporting; they do not relax or strengthen the associated symbolic constraints.

## Reproducibility cautions

- Several directories contain strict, relaxed, sliced, and manually seeded alternatives.  Compare results only when their initialization and constraint flags (`allow_weak`, `sum1`, `monotone_guard`, and `collisions`) match.
- A direct final-round classification and a decrypt-prune classification answer different questions.  `NEW_IV_ENC` intentionally demonstrates that they can differ.
- Benchmark scripts use their source-level default of 100 repetitions.
- Generated logs include the solver version, platform, duration, exit code, stdout, and stderr.  Re-running the suite replaces logs with the new local measurements.
