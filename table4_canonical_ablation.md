# Table 4 — canonical-ordering ablation

Metric: popped DFS occurrences, including repeats, dead ends, and pruned nodes.
Both variants are counted exhaustively. The direct engine is skipped for noncanonical myciel4 because an exhaustive run is computationally impractical.

| Instance | Variant | Memoised counter | Direct engine | Best χ | Counter/engine agreement | Paper count | Counter/paper agreement |
|---|---|---:|---:|---:|---|---:|---|
| myciel3.col | canonical | 2,325 | 2,325 | 4 | True | 2,325 | True |
| myciel3.col | noncanonical | 969,712 | 969,712 | 4 | True | 969,712 | True |
| myciel4.col | canonical | 929,315 | 929,315 | 5 | True | 929,315 | True |
| myciel4.col | noncanonical | 3,450,514,238,574,088 | not run | 5 | not applicable | 3,450,514,238,574,088 | True |

The canonical-ordering constraint reduces the popped-occurrence count of myciel3 from 969,712 to 2,325 (99.76%) and of myciel4 from 3,450,514,238,574,088 to 929,315 (approximately nine orders of magnitude).

Notes:
- The memoised counter and direct engine agree on all three cases where both were run: canonical and noncanonical myciel3, and canonical myciel4.
- The noncanonical myciel4 count is produced by the memoised counter only. An exhaustive direct-engine run was not attempted because its expected runtime is computationally impractical for this case; this is a runtime limitation, not a claim that DFS must retain all explored states in memory.
- Table 3 timeout counts and runtimes depend on the machine and execution environment. The exhaustive counts reported in Table 4 are deterministic.
