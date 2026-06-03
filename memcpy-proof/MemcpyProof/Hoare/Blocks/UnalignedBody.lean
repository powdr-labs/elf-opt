/-
The unaligned-16-byte loop **body** — parametrically over the shift
amounts `(sR, sL)` shared by B9, B20, B23.

  k = 1 → (sR, sL) = (24,  8)   (B9,  PCs 0x200998..0x2009f0)
  k = 2 → (sR, sL) = ( 8, 24)   (B20, PCs 0x200aa0..0x200af8)
  k = 3 → (sR, sL) = (16, 16)   (B23, PCs 0x200b28..0x200b80)

We split the 23-instr body into 5 sub-blocks of 6/5/5/4/3 to keep each
chunk's RComp nest shallow enough to typecheck quickly.

Strategy: we let Lean *infer* the composed-RComp post-condition for
each chunk (rather than spelling it out and miscounting parens), and
substitute every intermediate-state equation via `rfl` in the rintro
pattern — no separate `subst` chain.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Chunk 1 (6 instr): emits 1st dst word. -/

private def ub_c1 (sR sL : UInt32) : List Instr :=
  [ Instr.lw   16 13 0xFFFFFFF4
  , Instr.srli 15 15 sR
  , Instr.slli 17 16 sL
  , Instr.lw    5 13 0xFFFFFFF8
  , Instr.or_  15 17 15
  , Instr.sw   11 15 0
  ]

private def R_ub_c1 (sR sL : UInt32) : State → State → Prop :=
  fun s s' =>
    let a3 := getReg s 13
    let a5 := getReg s 15
    let w4 := loadWord s (a3 + 0xFFFFFFF4)
    let w3 := loadWord s (a3 + 0xFFFFFFF8)
    let out0 := (w4 <<< sL) ||| (a5 >>> sR)
    s'.pc = s.pc + 24 ∧
    getReg s' 11 = getReg s 11 ∧
    getReg s' 13 = a3 ∧
    getReg s' 15 = out0 ∧
    getReg s' 16 = w4 ∧
    getReg s' 17 = w4 <<< sL ∧
    getReg s' 5  = w3 ∧
    (∀ r : Fin 32, r.val ≠ 5 → r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord s (getReg s 11) out0).mem

private theorem ub_c1_triple (sR sL : UInt32) :
    Triple (ub_c1 sR sL) (R_ub_c1 sR sL) := by
  have h := ((Triple_lw   16 13 0xFFFFFFF4).append <|
             (Triple_srli 15 15 sR).append <|
             (Triple_slli 17 16 sL).append <|
             (Triple_lw    5 13 0xFFFFFFF8).append <|
             (Triple_or   15 17 15).append <|
             (Triple_sw   11 15 0))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 24 := by bv_decide
  simp [R_ub_c1, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h5' h15' h16' h17'
    simp [setReg, Ne.symm h5', Ne.symm h15', Ne.symm h16', Ne.symm h17']
  · unfold storeWord; simp [storeByte]

/-! ## Chunk 2 (5 instr): emits 2nd dst word. -/

private def ub_c2 (sR sL : UInt32) : List Instr :=
  [ Instr.srli 15 16 sR
  , Instr.slli 16  5 sL
  , Instr.lw   17 13 0xFFFFFFFC
  , Instr.or_  15 16 15
  , Instr.sw   11 15 4
  ]

private def R_ub_c2 (sR sL : UInt32) : State → State → Prop :=
  fun s s' =>
    let a3 := getReg s 13
    let a6 := getReg s 16
    let t0 := getReg s 5
    let w2 := loadWord s (a3 + 0xFFFFFFFC)
    let out4 := (t0 <<< sL) ||| (a6 >>> sR)
    s'.pc = s.pc + 20 ∧
    getReg s' 11 = getReg s 11 ∧
    getReg s' 13 = a3 ∧
    getReg s' 5  = t0 ∧
    getReg s' 15 = out4 ∧
    getReg s' 16 = t0 <<< sL ∧
    getReg s' 17 = w2 ∧
    (∀ r : Fin 32, r.val ≠ 5 → r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord s (getReg s 11 + 4) out4).mem

private theorem ub_c2_triple (sR sL : UInt32) :
    Triple (ub_c2 sR sL) (R_ub_c2 sR sL) := by
  have h := ((Triple_srli 15 16 sR).append <|
             (Triple_slli 16  5 sL).append <|
             (Triple_lw   17 13 0xFFFFFFFC).append <|
             (Triple_or   15 16 15).append <|
             (Triple_sw   11 15 4))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_ub_c2, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h5' h15' h16' h17'
    simp [setReg, Ne.symm h5', Ne.symm h15', Ne.symm h16', Ne.symm h17']
  · unfold storeWord; simp [storeByte]

/-! ## Chunk 3 (5 instr): emits 3rd dst word. -/

private def ub_c3 (sR sL : UInt32) : List Instr :=
  [ Instr.srli 16  5 sR
  , Instr.slli  5 17 sL
  , Instr.lw   15 13 0
  , Instr.or_  16  5 16
  , Instr.sw   11 16 8
  ]

private def R_ub_c3 (sR sL : UInt32) : State → State → Prop :=
  fun s s' =>
    let a3 := getReg s 13
    let t0 := getReg s 5
    let a7 := getReg s 17
    let w1 := loadWord s a3
    let out8 := (a7 <<< sL) ||| (t0 >>> sR)
    s'.pc = s.pc + 20 ∧
    getReg s' 11 = getReg s 11 ∧
    getReg s' 13 = a3 ∧
    getReg s' 15 = w1 ∧
    getReg s' 16 = out8 ∧
    getReg s' 17 = a7 ∧
    getReg s' 5  = a7 <<< sL ∧
    (∀ r : Fin 32, r.val ≠ 5 → r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord s (getReg s 11 + 8) out8).mem

private theorem ub_c3_triple (sR sL : UInt32) :
    Triple (ub_c3 sR sL) (R_ub_c3 sR sL) := by
  have h := ((Triple_srli 16  5 sR).append <|
             (Triple_slli  5 17 sL).append <|
             (Triple_lw   15 13 0).append <|
             (Triple_or   16  5 16).append <|
             (Triple_sw   11 16 8))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_ub_c3, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h5' h15' h16' h17'
    simp [setReg, Ne.symm h5', Ne.symm h15', Ne.symm h16', Ne.symm h17']
  · unfold storeWord; simp [storeByte]

/-! ## Chunk 4 (4 instr): emits 4th dst word. -/

private def ub_c4 (sR sL : UInt32) : List Instr :=
  [ Instr.srli 16 17 sR
  , Instr.slli 17 15 sL
  , Instr.or_  16 17 16
  , Instr.sw   11 16 12
  ]

private def R_ub_c4 (sR sL : UInt32) : State → State → Prop :=
  fun s s' =>
    let a5 := getReg s 15
    let a7 := getReg s 17
    let out12 := (a5 <<< sL) ||| (a7 >>> sR)
    s'.pc = s.pc + 16 ∧
    getReg s' 11 = getReg s 11 ∧
    getReg s' 13 = getReg s 13 ∧
    getReg s' 15 = a5 ∧
    getReg s' 16 = out12 ∧
    getReg s' 17 = a5 <<< sL ∧
    getReg s' 5  = getReg s 5 ∧
    (∀ r : Fin 32, r.val ≠ 16 → r.val ≠ 17 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord s (getReg s 11 + 12) out12).mem

private theorem ub_c4_triple (sR sL : UInt32) :
    Triple (ub_c4 sR sL) (R_ub_c4 sR sL) := by
  have h := ((Triple_srli 16 17 sR).append <|
             (Triple_slli 17 15 sL).append <|
             (Triple_or   16 17 16).append <|
             (Triple_sw   11 16 12))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 = s.pc + 16 := by bv_decide
  simp [R_ub_c4, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h16' h17'
    simp [setReg, Ne.symm h16', Ne.symm h17']
  · unfold storeWord; simp [storeByte]

/-! ## Chunk 5 (3 instr): pointer/count bumps only — no memory writes. -/

private def ub_c5 : List Instr :=
  [ Instr.addi 11 11 16
  , Instr.addi 12 12 0xFFFFFFF0
  , Instr.addi 13 13 16
  ]

private def R_ub_c5 : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 12 ∧
    getReg s' 11 = getReg s 11 + 16 ∧
    getReg s' 12 = getReg s 12 + 0xFFFFFFF0 ∧
    getReg s' 13 = getReg s 13 + 16 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

private theorem ub_c5_triple : Triple ub_c5 R_ub_c5 := by
  have h := ((Triple_addi 11 11 16).append <|
             (Triple_addi 12 12 0xFFFFFFF0).append <|
             (Triple_addi 13 13 16))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 = s.pc + 12 := by bv_decide
  simp [R_ub_c5, h_pc]
  intro r h11' h12' h13'
  simp [setReg, Ne.symm h11', Ne.symm h12', Ne.symm h13']

/-! ## The full block — `Triple.append` of the 5 chunks. -/

def mk_block_F_unaligned (sR sL : UInt32) : List Instr :=
  ub_c1 sR sL ++ ub_c2 sR sL ++ ub_c3 sR sL ++ ub_c4 sR sL ++ ub_c5

theorem mk_block_F_unaligned_triple_composed (sR sL : UInt32) :
    Triple (mk_block_F_unaligned sR sL)
      (RComp (R_ub_c1 sR sL)
        (RComp (R_ub_c2 sR sL)
          (RComp (R_ub_c3 sR sL)
            (RComp (R_ub_c4 sR sL) R_ub_c5)))) := by
  have h := (((ub_c1_triple sR sL).append (ub_c2_triple sR sL)).append
              ((ub_c3_triple sR sL).append (ub_c4_triple sR sL))).append
              ub_c5_triple
  refine Triple.weaken h ?_
  rintro s s' ⟨b, ⟨a, ⟨t1, h1, h2⟩, ⟨t2, h3, h4⟩⟩, h5⟩
  exact ⟨t1, h1, a, h2, t2, h3, b, h4, h5⟩

/-! ## The three specializations. -/

/-- B9 — unaligned-by-1 16-byte loop body (PCs 0x200998..0x2009f0). -/
def block_F_unaligned1 : List Instr := mk_block_F_unaligned 24 8

/-- B20 — unaligned-by-2 16-byte loop body (PCs 0x200aa0..0x200af8). -/
def block_F_unaligned2 : List Instr := mk_block_F_unaligned 8 24

/-- B23 — unaligned-by-3 16-byte loop body (PCs 0x200b28..0x200b80). -/
def block_F_unaligned3 : List Instr := mk_block_F_unaligned 16 16

end MemcpyProof.Hoare
