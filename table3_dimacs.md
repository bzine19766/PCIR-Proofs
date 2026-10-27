# Table 3 — DIMACS benchmark results

Per-instance timeout: 30.0 s.
Popped occurrences include repeated occurrences, dead ends, and pruned nodes.
A target reached before timeout is not an exhaustive proof.

| Group | Instance | |V| | |E| | Header edges | Target χ | Best found | Popped occurrences | Runtime (s) | Target reached | Exhaustive | Status |
|---|---|---:|---:|---|---:|---:|---:|---:|---|---|---|
| Small | myciel3.col | 11 | 20 | 20 (undirected) | 4 | 4 | 2325 | 0.014 | True | True | TARGET_REACHED_EXHAUSTIVE |
| Small | myciel4.col | 23 | 71 | 71 (undirected) | 5 | 5 | 929315 | 7.288 | True | True | TARGET_REACHED_EXHAUSTIVE |
| Small | queen5_5.col | 25 | 160 | 320 (doubled) | 5 | 5 | 4028236 | 30.000 | True | False | TARGET_REACHED_TIMEOUT |
| Medium | queen6_6.col | 36 | 290 | 580 (doubled) | 7 | 10 | 5227968 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
| Medium | myciel5.col | 47 | 236 | 236 (undirected) | 6 | 6 | 2350702 | 30.000 | True | False | TARGET_REACHED_TIMEOUT |
| Medium | queen7_7.col | 49 | 476 | 952 (doubled) | 7 | 10 | 4683306 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
| Medium | myciel6.col | 95 | 755 | 755 (undirected) | 7 | 7 | 2190301 | 30.000 | True | False | TARGET_REACHED_TIMEOUT |
| Medium | myciel7.col | 191 | 2360 | 2360 (undirected) | 8 | 8 | 2009923 | 30.000 | True | False | TARGET_REACHED_TIMEOUT |
| Large | queen8_8.col | 64 | 728 | 1456 (doubled) | 9 | 12 | 4561928 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
| Large | queen9_9.col | 81 | 1056 | 2112 (doubled) | 10 | 15 | 5015969 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
| Large | le450_5a.col | 450 | 5714 | 5714 (undirected) | 5 | 13 | 1466963 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
| Large | le450_5b.col | 450 | 5734 | 5734 (undirected) | 5 | 13 | 1878230 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
| Large | le450_15a.col | 450 | 8168 | 8168 (undirected) | 15 | 21 | 3281455 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
| Large | le450_25a.col | 450 | 8260 | 8260 (undirected) | 25 | 27 | 2926582 | 30.000 | False | False | TIMEOUT_TARGET_NOT_REACHED |
