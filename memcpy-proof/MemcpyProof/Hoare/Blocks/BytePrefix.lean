/-
B2 — the byte-prefix loop body (PCs 0x20090c..0x200940, 14 instr).

Copies one byte from `[a1]` to `[a0]` and advances pointers, then
computes in `a7` the loop-continuation predicate
`((a1+1) & 3 ≠ 0) ∧ (a2-1 ≠ 0)`.

Block layout (1-based step indices):

   1. addi a5, a1, 1      -- a5 ← a1 + 1   (probe pointer for align test)
   2. addi a6, a0, 0      -- a6 ← a0
   3. lb   a7, 0(a1)      -- a7 ← signExt(Mem[a1])
   4. addi a4, a1, 1      -- a4 ← a1 + 1   (saved next-a1)
   5. addi a3, a6, 1      -- a3 ← a0 + 1   (saved next-a0)
   6. sb   a7, 0(a6)      -- Mem[a0] ← (a7 as UInt8)
   7. addi a2, a2, -1     -- a2 ← a2 - 1
   8. andi a1, a5, 3      -- a1 ← (a1+1) & 3
   9. sltu a1, zero, a1   -- a1 ← (0 < a1)  ? 1 : 0
  10. sltu a6, zero, a2   -- a6 ← (0 < a2)  ? 1 : 0
  11. and  a7, a1, a6     -- a7 ← a1 & a6  (= "loop again" flag)
  12. addi a5, a5, 1      -- a5 ← a1 + 2
  13. addi a1, a4, 0      -- a1 ← a1 + 1
  14. addi a6, a3, 0      -- a6 ← a0 + 1

Split into 5 / 5 / 4 chunks.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Chunk 1 (5 instr): byte-load + address-setup. -/

private def bp_c1 : List Instr :=
  [ Instr.addi 15 11 1
  , Instr.addi 16 10 0
  , Instr.lb   17 11 0
  , Instr.addi 14 11 1
  , Instr.addi 13 16 1
  ]

private def R_bp_c1 : State → State → Prop :=
  fun s s' =>
    let a0 := getReg s 10
    let a1 := getReg s 11
    s'.pc = s.pc + 20 ∧
    getReg s' 13 = a0 + 1 ∧
    getReg s' 14 = a1 + 1 ∧
    getReg s' 15 = a1 + 1 ∧
    getReg s' 16 = a0 ∧
    getReg s' 17 = signExt (loadByte s a1).toUInt32 7 ∧
    (∀ r : Fin 32, r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 15 → r.val ≠ 16 →
       r.val ≠ 17 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

private theorem bp_c1_triple : Triple bp_c1 R_bp_c1 := by
  have h := ((Triple_addi 15 11 1).append <|
             (Triple_addi 16 10 0).append <|
             (Triple_lb   17 11 0).append <|
             (Triple_addi 14 11 1).append <|
             (Triple_addi 13 16 1))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_bp_c1, h_pc]
  intro r h13 h14 h15 h16 h17
  simp [setReg, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17]

/-! ## Chunk 2 (5 instr): byte-store + loop-predicate parts. -/

private def bp_c2 : List Instr :=
  [ Instr.sb   16 17 0
  , Instr.addi 12 12 0xFFFFFFFF
  , Instr.andi 11 15 3
  , Instr.sltu 11 0 11
  , Instr.sltu 16 0 12
  ]

private def R_bp_c2 : State → State → Prop :=
  fun s s' =>
    let a2' := getReg s 12 + 0xFFFFFFFF
    s'.pc = s.pc + 20 ∧
    getReg s' 11 = (if 0 < (getReg s 15 &&& 3) then 1 else 0) ∧
    getReg s' 12 = a2' ∧
    getReg s' 16 = (if 0 < a2' then 1 else 0) ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 16 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte s (getReg s 16) (getReg s 17).toUInt8).mem

private theorem bp_c2_triple : Triple bp_c2 R_bp_c2 := by
  have h := ((Triple_sb   16 17 0).append <|
             (Triple_addi 12 12 0xFFFFFFFF).append <|
             (Triple_andi 11 15 3).append <|
             (Triple_sltu 11 0 11).append <|
             (Triple_sltu 16 0 12))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_bp_c2, h_pc]
  intro r h11 h12 h16
  simp [setReg, Ne.symm h11, Ne.symm h12, Ne.symm h16]

/-! ## Chunk 3 (4 instr): bitwise-and the two predicate bits + pointer bumps. -/

private def bp_c3 : List Instr :=
  [ Instr.and_ 17 11 16
  , Instr.addi 15 15 1
  , Instr.addi 11 14 0
  , Instr.addi 16 13 0
  ]

private def R_bp_c3 : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 16 ∧
    getReg s' 11 = getReg s 14 ∧
    getReg s' 15 = getReg s 15 + 1 ∧
    getReg s' 16 = getReg s 13 ∧
    getReg s' 17 = getReg s 11 &&& getReg s 16 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

private theorem bp_c3_triple : Triple bp_c3 R_bp_c3 := by
  have h := ((Triple_and  17 11 16).append <|
             (Triple_addi 15 15 1).append <|
             (Triple_addi 11 14 0).append <|
             (Triple_addi 16 13 0))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 = s.pc + 16 := by bv_decide
  simp [R_bp_c3, h_pc]
  intro r h11 h15 h16 h17
  simp [setReg, Ne.symm h11, Ne.symm h15, Ne.symm h16, Ne.symm h17]

/-! ## The full block — `Triple.append` of the 3 chunks. -/

def block_byte_prefix_body : List Instr := bp_c1 ++ bp_c2 ++ bp_c3

theorem block_byte_prefix_body_triple_composed :
    Triple block_byte_prefix_body
      (RComp R_bp_c1 (RComp R_bp_c2 R_bp_c3)) := by
  have h := (bp_c1_triple.append bp_c2_triple).append bp_c3_triple
  refine Triple.weaken h ?_
  -- left-associated `RComp (RComp R_c1 R_c2) R_c3` → right-associated.
  rintro s s' ⟨t2, ⟨t1, h1, h2⟩, h3⟩
  exact ⟨t1, h1, t2, h2, h3⟩

end MemcpyProof.Hoare
