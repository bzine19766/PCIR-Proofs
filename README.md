# PCIR-Proofs
Machine-checked Isabelle/HOL proofs for the PCIR (Parallel Coloring Iterative Refinement) algorithm for exact graph coloring.
# PCIR-Proofs

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

The theories are organised into independent Isabelle/HOL modules covering

- Graph definitions
- Configuration semantics
- Transition rules
- Operational updates
- Invariants
- Ranking function
- Reachability
- Transition inversion
- Unique predecessor property
- Soundness theorem
- Completeness theorem
- Correctness theorem

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



# Citation

If you use this repository, please cite

> Zine El Abidine Bouneb and Jim Woodcock,
> **A Configuration-State Semantics for MIS-Cover Graph Coloring**,
> 2026.

---

# License

MIT License.
