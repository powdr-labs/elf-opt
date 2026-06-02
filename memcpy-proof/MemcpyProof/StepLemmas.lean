/-
Lemmas for symbolic execution of the extracted memcpy.

Strategy:
* register accesses go via `getReg` / `setReg` which we make `simp`-friendly
* instruction fetch + decode is concrete (the code is hard-coded in
  `Extract.lean`) so `simp` can fully reduce `step code s` once `s.pc` is
  a literal.
* branch conditions are the hard part: when the value depends only on
  the symbolic input register, we resolve them by case analysis or by
  one of the bit-level helper lemmas below.
-/

import MemcpyProof.Sem
import MemcpyProof.Extract
import MemcpyProof.Harness

namespace MemcpyProof.StepLemmas

open MemcpyProof.Sem
open MemcpyProof.Extract
open MemcpyProof.Harness

/-! ## Register file simp lemmas. -/

@[simp] theorem getReg_x0 (s : State) : getReg s 0 = 0 := by
  unfold getReg; simp

theorem getReg_setReg_same {s : State} {r v : UInt32} (h : r ≠ 0) :
    getReg (setReg s r v) r = v := by
  unfold getReg setReg
  simp [h]

theorem getReg_setReg_other {s : State} {r r' v : UInt32}
    (h : r ≠ r') :
    getReg (setReg s r v) r' = getReg s r' := by
  unfold getReg setReg
  by_cases h0 : r = 0
  · simp [h0]
  · simp [h0]
    by_cases hz : r' = 0
    · simp [hz]
    · simp [hz]
      intro contra
      exact (h contra.symm).elim

/-! ## A single concrete instruction step.

These are the workhorses: given a current PC equal to a literal address,
unfold `step` → `decode` → `exec` to the post-state expression. -/

theorem step_unfold (code : CodeFn) (s : State) (hh : s.halted = false) :
    step code s = exec s (MemcpyProof.RV32I.decode (code s.pc)) := by
  unfold step
  simp [hh]

end MemcpyProof.StepLemmas
