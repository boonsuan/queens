import Queens.DiagonalCoverage
import Queens.Finite.Reachability
import Queens.KnuthRanges
import Queens.LowerRunCoverage
import Queens.RepeatedRunCoverage

/-!
# Greedy Queens and the Golden Ratio

`Queens.main` proves Theorem 1, the paper's two strict golden-ratio bounds for
the actual least-unattacked-row sequence, and `Queens.knuth_bounds` proves
Theorem 2, the sharper bounds that give Knuth's ranges. Corollaries 19 and 20
are proved as well. See README.md for the paper-to-code map, the scope exclusions,
and the kernel-checked finite verification with its explicit axiom audit.
-/
