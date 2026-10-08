# PCIR_Proofs

Machine-checked Isabelle/HOL proofs for the PCIR (Parallel Coloring Iterative Refinement) algorithm for exact graph coloring.

# PCIR_Proofs

Machine-checked Isabelle/HOL proofs accompanying the paper

> **A Configuration-State Semantics for MIS-Cover Graph Coloring**

by

**Dr. Zine El Abidine Bouneb**  
University of Oum El Bouaghi, Algeria

**Prof. Jim Woodcock**  
University of York, United Kingdom

---

## Overview

This repository contains the complete Isabelle/HOL formalization of the operational semantics presented in the paper *A Configuration-State Semantics for MIS-Cover Graph Coloring*.

The development formalizes the semantics of MIS-cover graph coloring using configuration states

\[
\Gamma = (P,R,I,C)
\]

where

- **P** is the residual vertex pool,
- **R** is the list of committed maximal independent sets (color classes),
- **I** is the current maximal independent set under construction,
- **C** is the candidate workspace.

The semantics is specified as a labelled transition system and verified entirely in Isabelle/HOL.

---

# Quick Start

```bash
# 1. Unzip the archive
unzip PCIR_Proofs.zip
cd PCIR_Proofs

# 2. Build the whole session from scratch (recommended for first run)
isabelle build -c -v -D . MIS_Cover

# 3. (Optional) Open the development in Isabelle/jEdit
isabelle jedit -d . MIS_Cover_Semantics.thy
```

If the build succeeds you will see, at the end of the log:

```
Finished MIS_Cover (0:00:37 elapsed time, 0:01:34 cpu time, ...)
```

---

# Formal Results

The repository contains machine-checked proofs of:

- Operational transition semantics
- Configuration well-formedness
- Structural invariants
- Reachability
- Ranking function
- Transition preservation
- Uniqueness of predecessors
- Rooted-tree property of the configuration graph
- Unique path property
- Soundness
- Completeness
- Correctness of the generated graph coloring

All proofs are fully mechanized in Isabelle/HOL.

---

# Repository Structure

The development is organised as a single Isabelle/HOL session, `MIS_Cover`, whose root theory file (`ROOT`) lists six independent theory modules. The dependency order is linear: each theory imports the previous one, so the whole session builds from scratch in one pass.

```
PCIR_Proofs/
├── ROOT                              # Isabelle session root (declares session MIS_Cover)
├── MIS_Cover.thy                     # Session entry point (imports the six theories)
├── MIS_Cover_Semantics.thy           # Graph, config, transitions, invariants, ranking
├── MIS_Commit_Bijection.thy          # Canonical ADD paths; MIS ↔ commit-ready bijection
├── MIS_Soundness_Completeness.thy    # Soundness (terminal ⟹ coloring) and completeness
├── MIS_Universal.thy                 # Termination, finiteness, optimality, universal completeness
├── MIS_Structure.thy                 # Unique predecessor, rooted tree, partial order, self-containment
├── MIS_Paw.thy                       # Paw Graph example (37 states, 6 terminals, 2 dead ends)
└── README.md                         # This file
```

### Theory dependency graph

```
MIS_Cover_Semantics
        │
        ▼
MIS_Commit_Bijection
        │
        ▼
MIS_Soundness_Completeness
        │
        ▼
MIS_Universal
        │
        ▼
MIS_Structure
        │
        ▼
MIS_Paw
```

Each arrow denotes an `imports` dependency. Because the order is linear, no theory can be built before its predecessor.

### Module summary

| Theory file | Contents |
|---|---|
| `MIS_Cover_Semantics.thy` | Locale `fixed_graph`; `config` type synonym; definitions `is_indep`, `is_maximal_indep`, `candidate_set`, `well_formed`, `\<Gamma>0`; inductive `step` (ADD / COMMIT); `reachable`, `ReachG`; ranking function `\<rho>`; lemmas `candidate_set_mem_iff`, `indep_add`, `wf_add`, `wf_commit`, `rho_add`, `rho_commit`, `\<rho>_strict_decrease`, `invariant_preservation`, `reachable_well_formed`. |
| `MIS_Commit_Bijection.thy` | Inductive `add_path_seq`; `MIS_P`, `commit_ready_states`, `\<Phi>`; lemmas `add_path_seq_candidate`, `add_path_seq_imp_reachable`, `set_of_add_path_seq`, `sorted_add_path_seq`, `strict_sorted_set_unique`, `add_path_seq_unique`, `exists_sorted_enum`, `list_to_add_path_seq`; theorem `theorem_6_1_MIS_Commit_Ready_Bijection`. |
| `MIS_Soundness_Completeness.thy` | `is_valid_coloring`, `chromatic_num`, `is_terminal`; bridging lemmas `index_disjoint_distinct`, `index_disjoint_set_disjoint`; coloring manipulation lemmas `valid_coloring_snoc_split`, `valid_coloring_snoc`, `valid_coloring_remove`, `valid_coloring_exists`; chromatic-number lemmas; `independent_set_extension`; `lemma_8_1_MIS_chromatic_recurrence`; `theorem_8_1_Soundness`; `theorem_8_2_Residual_Completeness`; `corollary_8_1_Global_Completeness`. |
| `MIS_Universal.thy` | `rsize`, `is_dead_end`; `step_enabled`, `terminal_stuck`, `dead_end_stuck`, `stuck_terminal_or_dead_end`; `universal_termination`; `lenbound`, `lenbound_step`, `finite_ReachG`; `terminal_sizes`, `universal_lower_bound`, `optimality_exhaustive`; `commit_phase`, `completeness_colorings_aux`, `completeness_for_colorings`, `global_completeness_for_colorings`. |
| `MIS_Structure.thy` | `step_unfold`; `add_pred_unique`, `commit_pred_unique`, `step_pred_unique`, `unique_predecessor`; inductive `path`, `path_unique_aux`, `unique_path`, `acyclic_reach`, `rooted_tree`; `partial_order_reach`, `least_element`, `root_minimal`, `unique_minimal`; `ancestors_comparable`, `sibling_not_below`, `disjoint_subtrees`; `enabled_iff`, `self_containment`, `finite_branching`. |
| `MIS_Paw.thy` | Concrete instantiation of the semantics on the Paw Graph; verification of the counts 37 reachable configurations, 36 transitions, 6 terminals, 2 dead ends, chromatic number 3 (`Paw_terminal_count`, `Paw_chromatic`). |

---

# How to Compile

## Prerequisites

- **Isabelle2025** (or Isabelle2025-2). Download from <https://isabelle.in.tum.de/>.
- A Java runtime is bundled with Isabelle — no separate JDK installation is required.
- Roughly 2 GB of free disk space for the Isabelle distribution and the `HOL` image.

Verify your installation by running:

```bash
isabelle version
```

You should see the version string (e.g. `Isabelle2025-2`).

## Step 1 — Obtain the archive

Download `PCIR_Proofs.zip` from the repository and unzip it:

```bash
unzip PCIR_Proofs.zip
cd PCIR_Proofs
```

After unzipping, the directory must contain the `ROOT` file and the six `.thy` files listed in the *Repository Structure* section above.

## Step 2 — Build from the root

From the directory that contains `ROOT`, run:

```bash
isabelle build -c -v -D . MIS_Cover
```

Flag-by-flag explanation:

| Flag | Meaning |
|---|---|
| `-c` | **Clean build.** Delete any previously built heap images for this session before rebuilding. Use this on a first run, or whenever you have edited a theory file and want a fully reproducible build. |
| `-v` | **Verbose.** Print progress information for each theory as it is processed. |
| `-D .` | **Directory.** Use the current directory (`.`) as the session directory — i.e. look for `ROOT` here. |
| `MIS_Cover` | The name of the session to build (as declared in `ROOT`). |

The first build also compiles the `HOL` image if it is not already present; this can take several minutes. Subsequent builds are much faster.

### Expected output (tail)

```
Building HOL ...
Finished HOL (0:01:12 elapsed time, ...)
Running MIS_Cover ...
MIS_Cover_Semantics: ...
MIS_Commit_Bijection: ...
MIS_Soundness_Completeness: ...
MIS_Universal: ...
MIS_Structure: ...
MIS_Paw: ...
Finished MIS_Cover (0:00:37 elapsed time, 0:01:34 cpu time, ...)
```

The exact timings depend on your machine; the paper reports about **37 seconds** for the `MIS_Cover` session on an Intel I5 with Isabelle2025-2.

<img width="1366" height="768" alt="run" src="https://github.com/user-attachments/assets/3d10d248-4ee8-4568-b1fb-e391d954ec6b" />

## Step 3 — Build without cleaning (incremental)

If you have already built the session once and have only changed one theory, you can omit `-c` to reuse existing heap images:

```bash
isabelle build -v -D . MIS_Cover
```

Isabelle will rebuild only the theories affected by your change.

## Step 4 — Open the development in Isabelle/jEdit

To browse and interact with the proofs:

```bash
isabelle jedit -d . MIS_Cover_Semantics.thy
```

Replace `MIS_Cover_Semantics.thy` with any of the six theory files to open it directly. The `-d .` flag tells jEdit to use the current directory as the session directory. From inside jEdit you can also open the other theories via *File → Open*; the session `MIS_Cover` will appear in the *Theories* panel.

## Step 5 — Build a specific theory only

To build just one theory (and its dependencies), pass the theory name without the `.thy` extension:

```bash
isabelle build -c -v -D . MIS_Structure
```

This is useful when you want to verify a single module quickly.

## Step 6 — Clean up

To remove all build artifacts (heap images, log files) and return to a pristine source tree:

```bash
isabelle build -c -D . MIS_Cover   # rebuild with -c already cleans the session
# or, to remove everything:
rm -rf output/
```

---

## Troubleshooting

| Symptom | Cause | Fix |
|---|---|---|
| `Bad session directory` | You ran `isabelle build` from outside the directory containing `ROOT`. | `cd` into the unzipped `PCIR_Proofs` directory first. |
| `Unknown session MIS_Cover` | The `ROOT` file is missing or misnamed. | Ensure `ROOT` (no extension) is present in the current directory. |
| Build hangs on `HOL` | First-time compilation of the `HOL` image. | Wait — this is normal on a first run. |
| `Cannot find theory` | A theory file is missing or renamed. | Check that all six `.thy` files are present alongside `ROOT`. |
| Out-of-memory during build | Insufficient heap for `HOL`. | Increase the heap size in `ROOT` via `options [heap = 2000]` (values in MB). |
| `isabelle: command not found` | Isabelle's `bin` directory is not on `PATH`. | Add `<isabelle-distribution>/bin` to `PATH`, or invoke `isabelle` by absolute path. |

---

# Research Contributions

The accompanying paper establishes that the configuration-state semantics satisfies several important theoretical properties.

These include

- rooted-tree structure of the configuration graph;
- uniqueness of every root-to-configuration execution path;
- elimination of redundant configuration exploration;
- preservation of structural invariants;
- serializability of configuration states;
- parallel decomposition of sibling configurations;
- constructive soundness and completeness proofs.

These results provide a formal foundation for asynchronous and distributed exact graph coloring based on maximal independent set decomposition.

---

# Contribution Statement

This work was carried out through close collaboration.

- **Dr. Zine El Abidine Bouneb** developed the original PCIR (Parallel Coloring Iterative Refinement) algorithm, the configuration-state model, and the underlying graph coloring methodology.

- **Prof. Jim Woodcock** supervised the formal methods aspect of the work, proposed presenting the algorithm as a configuration-state semantics, guided the mathematical structure of the correctness proofs, and introduced the use of Isabelle/HOL for the verification.

- The complete Isabelle/HOL formalization contained in this repository was implemented by **Dr. Zine El Abidine Bouneb** under the supervision of **Prof. Jim Woodcock**.

Both authors contributed substantially to the resulting research and share responsibility for the scientific contribution presented in the accompanying paper.

---

# Requirements

- Isabelle2025

---

# Citation

If you use this repository, please cite

> Zine El Abidine Bouneb and Jim Woodcock,
> **A Configuration-State Semantics for MIS-Cover Graph Coloring**,
> 2026.

---

# License

MIT License.
