import Queens.RepeatedRuns
import Queens.RunsCoverage

/-!
# Every term belongs to a finite repeated run

Corollary 19's A275887 records maximal repetitions in `lowerRunLength` (A275885).
The exclusion of twelve consecutive equal terms ensures that this description
accounts for every term, with no infinite constant tail. Applying generic run
uniqueness identifies its finite maximal run.
-/

namespace Queens

/-- **Corollary 19, A275887 coverage:** every term of A275885 belongs to a
unique finite maximal repetition of that value. Thus the exact range theorem
for repeated run lengths describes the entire sequence of repetitions. -/
theorem existsUnique_repeated_lower_run_contains (n : ℕ) :
    ∃! interval : ℕ × ℕ,
      Sequence.MaximalRun (fun k => lowerRunLength k = lowerRunLength n)
        interval.1 interval.2 ∧
      interval.1 ≤ n ∧ n < interval.1 + interval.2 := by
  exact Sequence.existsUnique_maximalRun_contains
    (bound := 11) (fun s => no_twelve_equal_lower_run_lengths s (lowerRunLength n)) rfl

end Queens
