import Queens.DiagonalCoverage
import Queens.Finite.Reachability
import Queens.SharperBounds
import Queens.LowerRunCoverage
import Queens.RepeatedRunCoverage

/-!
# Greedy Queens and the Golden Ratio

`Queens.main` proves the paper's two strict golden-ratio bounds for the actual
least-unattacked-row sequence. Corollaries 18–19, Lemma 20, and Proposition 21
are proved as well. See README.md for the paper-to-code map, the scope exclusions,
and the kernel-checked finite verification with its explicit axiom audit.
-/
