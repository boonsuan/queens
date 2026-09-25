import Queens
import Lean.Util.CollectAxioms

/-!
# Reproducible axiom audit

These commands inspect the actual proof dependencies, including the finite
certificates. `scripts/check_axioms.py` requires every listed result to use only
`propext`, `Classical.choice`, and `Quot.sound`. In particular, a compiler-evaluation
axiom or an accidentally admitted proof makes the audit fail.
-/

#print axioms Queens.q_bijective
#print axioms Queens.sortedLowerRow_eq
#print axioms Queens.count_error_lt
#print axioms Queens.main_of_diagonalDiscrepancy
#print axioms Queens.Finite.historyGraph_wellFormed
#print axioms Queens.Finite.certificate_checked
#print axioms Queens.Finite.initialState_represented
#print axioms Queens.main_of_localStepExact

#print axioms Queens.local_step_exact
#print axioms Queens.bounded_diagonal_discrepancy
#print axioms Queens.main
#print axioms Queens.Finite.certified_iff_reachable
#print axioms Queens.Finite.reached_state_count
#print axioms Queens.Finite.reached_edge_count

#print axioms Queens.q_diagonal_bijective
#print axioms Queens.lowerDiagonal_bijOn

#print axioms Queens.exact_error_recursion
#print axioms Queens.referenceLowerRank_lt
#print axioms Queens.Finite.prefix_sharp_count_error
#print axioms Queens.Finite.sharp_certificate_checked
#print axioms Queens.sharp_count_error
#print axioms Queens.sharper_bounds

#print axioms Queens.lower_column_run_lengths
#print axioms Queens.upper_column_run_lengths
#print axioms Queens.upper_column_gaps
#print axioms Queens.lower_column_gaps
#print axioms Queens.lowerRunLength_range
#print axioms Queens.existsUnique_lowerRun_of_maximal
#print axioms Queens.Finite.Forty.historyGraph_wellFormed
#print axioms Queens.Finite.Forty.certificate_checked
#print axioms Queens.Finite.Forty.initialState_represented
#print axioms Queens.Finite.Forty.actualVertex_represents
#print axioms Queens.Finite.repeatedRunCertificate
#print axioms Queens.repeated_lower_run_lengths
#print axioms Queens.no_ten_repeated_lower_runs
#print axioms Queens.no_twelve_equal_lower_run_lengths
#print axioms Queens.existsUnique_repeated_lower_run_contains

-- Inspect every imported project declaration as well as the named results.
-- Module ownership includes private helpers and generated certificate pieces.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if (`Queens).isPrefixOf moduleName then
        let axioms ← collectAxioms name
        let extra := axioms.filter fun ax => !allowed.contains ax
        unless extra.isEmpty do
          throwError "{name} has disallowed axiom dependencies: {extra}"
        count := count + 1
  if count == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Kernel-only audit passed for all {count} imported project declarations."
