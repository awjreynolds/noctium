import Noctium.Verification.NativeState

namespace Noctium.Verification.NativeStateReadTape

open NativeState

/-- The cells named by popeq operations, in execution order. A skipped
operation is absent from the operation list and contributes no expected read. -/
def expectedCells (ops : List NativeState.Op) : List NativeState.Cell :=
  ops.filterMap fun
    | .popeq expected => some expected
    | _ => none

private theorem step_reads {op : NativeState.Op} {before after : NativeState.Machine}
    (stepped : NativeState.step op before = some after) :
    after.reads = before.reads ++ expectedCells [op] := by
  rcases before with ⟨stack, reads⟩
  rcases after with ⟨afterStack, afterReads⟩
  unfold NativeState.step at stepped
  dsimp only at stepped
  split at stepped
  all_goals simp_all [expectedCells, Bind.bind, Option.bind]
  all_goals repeat' (split at stepped <;> simp_all)
  case h_6 slot key items rest =>
    cases selected : items[slot]? with
    | none => simp [selected] at stepped
    | some target =>
      cases target with
      | cell value => simp [selected] at stepped
      | map entries =>
        cases found : entries.lookup key <;> simp_all

/-- A successful VM run appends exactly the expected cells for its executed
popeq operations. The equality check remains part of the run premise. -/
theorem run_reads {ops : List NativeState.Op} {before after : NativeState.Machine}
    (run : NativeState.run ops before = some after) :
    after.reads = before.reads ++ expectedCells ops := by
  induction ops generalizing before with
  | nil =>
      simp [NativeState.run] at run
      cases run
      simp [expectedCells]
  | cons op ops ih =>
      cases stepped : NativeState.step op before with
      | none => simp [NativeState.run, stepped] at run
      | some middle =>
          have tailRun : NativeState.run ops middle = some after := by
            simpa [NativeState.run, stepped] using run
          have tailReads := ih tailRun
          rw [tailReads, step_reads stepped]
          cases op <;> simp [expectedCells]

end Noctium.Verification.NativeStateReadTape
