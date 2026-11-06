import FinalFinal
import Lean.Util.CollectAxioms

/-! Audit every imported declaration in the Cylinder namespace, including
the manuscript-specific additions. Unexpected proof axioms cause failure. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut failed : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (decl, _) in env.constants.toList do
    if (`Cylinder).isPrefixOf decl then
      let axioms ← Lean.collectAxioms decl
      checked := checked + 1
      logInfo m!"AXIOMS|{decl}|{axioms.toList}"
      for ax in axioms do
        unless allowed.contains ax do
          failed := failed + 1
          logError m!"UNEXPECTED_AXIOM|{decl}|{ax}"
  if checked == 0 then
    throwError "No Cylinder declarations found"
  logInfo m!"CURRENT_AUDIT_SUMMARY|checked={checked}|unexpected={failed}"
  if failed != 0 then
    throwError "Unexpected axiom dependencies found"
