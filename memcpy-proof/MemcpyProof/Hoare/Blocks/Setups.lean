/-
The four setup/preamble blocks:

  * B11 — `setup_align`         (3 instr, PCs 0x200a00..0x200a08)
  * B19 — `F_unaligned2_setup`  (6 instr, PCs 0x200a88..0x200a9c)
  * B22 — `F_unaligned3_setup`  (8 instr, PCs 0x200b08..0x200b24)
  * B8  — `F_unaligned1_setup`  (10 instr, PCs 0x200970..0x200994)

Each is a straight-line preamble executed once before entering its
loop body.  Plain `Triple.append` + `Triple.weaken` patterns.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## B11 — `setup_align` (3 instr).

  addi a3, a0, 0      -- copy dst pointer
  addi a4, a1, 0      -- copy src pointer
  andi a1, a3, 3      -- compute dst alignment -/

def block_setup_align : List Instr :=
  [ Instr.addi 13 10 0
  , Instr.addi 14 11 0
  , Instr.andi 11 13 3
  ]

theorem block_setup_align_triple_composed :
    Triple block_setup_align
      (RComp (fun s s' => s' = advance (setReg s 13 (getReg s 10 + 0)))
        (RComp (fun s s' => s' = advance (setReg s 14 (getReg s 11 + 0)))
               (fun s s' => s' = advance (setReg s 11 (getReg s 13 &&& 3))))) :=
  (Triple_addi 13 10 0).append <|
  (Triple_addi 14 11 0).append <|
  (Triple_andi 11 13 3)

def R_block_setup_align : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 12 ∧
    getReg s' 11 = getReg s 10 &&& 3 ∧
    getReg s' 13 = getReg s 10 ∧
    getReg s' 14 = getReg s 11 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 13 → r.val ≠ 14 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

theorem block_setup_align_triple :
    Triple block_setup_align R_block_setup_align := by
  refine Triple.weaken block_setup_align_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 = s.pc + 12 := by bv_decide
  simp [R_block_setup_align, h_pc]
  intro r hr11 hr13 hr14
  simp [setReg, Ne.symm hr11, Ne.symm hr13, Ne.symm hr14]

/-! ## B19 — `F_unaligned2_setup` (6 instr).

  lw   a5, 0(a4)         -- a5 ← Mem[a4]
  addi a1, a3, 1
  sb   a5, 0(a3)
  addi a2, a2, -1
  addi a3, a4, 16
  addi a4, zero, 18 -/

def block_F_unaligned2_setup : List Instr :=
  [ Instr.lw   15 14 0
  , Instr.addi 11 13 1
  , Instr.sb   13 15 0
  , Instr.addi 12 12 0xFFFFFFFF
  , Instr.addi 13 14 16
  , Instr.addi 14 0 18
  ]

theorem block_F_unaligned2_setup_triple_composed :
    Triple block_F_unaligned2_setup
      (RComp (fun s s' => s' = advance (setReg s 15 (loadWord s (getReg s 14 + 0))))
        (RComp (fun s s' => s' = advance (setReg s 11 (getReg s 13 + 1)))
          (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 0) (getReg s 15).toUInt8))
            (RComp (fun s s' => s' = advance (setReg s 12 (getReg s 12 + 0xFFFFFFFF)))
              (RComp (fun s s' => s' = advance (setReg s 13 (getReg s 14 + 16)))
                    (fun s s' => s' = advance (setReg s 14 (getReg s 0 + 18))))))))  :=
  (Triple_lw   15 14 0).append <|
  (Triple_addi 11 13 1).append <|
  (Triple_sb   13 15 0).append <|
  (Triple_addi 12 12 0xFFFFFFFF).append <|
  (Triple_addi 13 14 16).append <|
  (Triple_addi 14 0 18)

def R_block_F_unaligned2_setup : State → State → Prop :=
  fun s s' =>
    let v0 : UInt32 := loadWord s (getReg s 14)
    s'.pc = s.pc + 24 ∧
    getReg s' 11 = getReg s 13 + 1 ∧
    getReg s' 12 = getReg s 12 + 0xFFFFFFFF ∧
    getReg s' 13 = getReg s 14 + 16 ∧
    getReg s' 14 = 18 ∧
    getReg s' 15 = v0 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 15 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte s (getReg s 13) v0.toUInt8).mem

theorem block_F_unaligned2_setup_triple :
    Triple block_F_unaligned2_setup R_block_F_unaligned2_setup := by
  refine Triple.weaken block_F_unaligned2_setup_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 24 := by bv_decide
  simp [R_block_F_unaligned2_setup, h_pc]
  refine ⟨?_, ?_⟩
  · intro r hr11 hr12 hr13 hr14 hr15
    simp [setReg, Ne.symm hr11, Ne.symm hr12, Ne.symm hr13, Ne.symm hr14, Ne.symm hr15]
  · unfold storeByte; simp

/-! ## B22 — `F_unaligned3_setup` (8 instr).

  lw   a5, 0(a4)         -- a5 ← Mem[a4]
  sb   a5, 0(a3)
  srli a6, a5, 8
  addi a1, a3, 2
  sb   a6, 1(a3)
  addi a2, a2, -2
  addi a3, a4, 16
  addi a4, zero, 17 -/

def block_F_unaligned3_setup : List Instr :=
  [ Instr.lw   15 14 0
  , Instr.sb   13 15 0
  , Instr.srli 16 15 8
  , Instr.addi 11 13 2
  , Instr.sb   13 16 1
  , Instr.addi 12 12 0xFFFFFFFE
  , Instr.addi 13 14 16
  , Instr.addi 14 0 17
  ]

theorem block_F_unaligned3_setup_triple_composed :
    Triple block_F_unaligned3_setup
      (RComp (fun s s' => s' = advance (setReg s 15 (loadWord s (getReg s 14 + 0))))
        (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 0) (getReg s 15).toUInt8))
          (RComp (fun s s' => s' = advance (setReg s 16 (getReg s 15 >>> 8)))
            (RComp (fun s s' => s' = advance (setReg s 11 (getReg s 13 + 2)))
              (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 1) (getReg s 16).toUInt8))
                (RComp (fun s s' => s' = advance (setReg s 12 (getReg s 12 + 0xFFFFFFFE)))
                  (RComp (fun s s' => s' = advance (setReg s 13 (getReg s 14 + 16)))
                        (fun s s' => s' = advance (setReg s 14 (getReg s 0 + 17))))))))))  :=
  (Triple_lw   15 14 0).append <|
  (Triple_sb   13 15 0).append <|
  (Triple_srli 16 15 8).append <|
  (Triple_addi 11 13 2).append <|
  (Triple_sb   13 16 1).append <|
  (Triple_addi 12 12 0xFFFFFFFE).append <|
  (Triple_addi 13 14 16).append <|
  (Triple_addi 14 0 17)

def R_block_F_unaligned3_setup : State → State → Prop :=
  fun s s' =>
    let v0 : UInt32 := loadWord s (getReg s 14)
    s'.pc = s.pc + 32 ∧
    getReg s' 11 = getReg s 13 + 2 ∧
    getReg s' 12 = getReg s 12 + 0xFFFFFFFE ∧
    getReg s' 13 = getReg s 14 + 16 ∧
    getReg s' 14 = 17 ∧
    getReg s' 15 = v0 ∧
    getReg s' 16 = v0 >>> 8 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
       r.val ≠ 15 → r.val ≠ 16 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte (storeByte s (getReg s 13) v0.toUInt8)
                        (getReg s 13 + 1) (v0 >>> 8).toUInt8).mem

theorem block_F_unaligned3_setup_triple :
    Triple block_F_unaligned3_setup R_block_F_unaligned3_setup := by
  refine Triple.weaken block_F_unaligned3_setup_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 32 := by bv_decide
  simp [R_block_F_unaligned3_setup, h_pc]
  refine ⟨?_, ?_⟩
  · intro r hr11 hr12 hr13 hr14 hr15 hr16
    simp [setReg, Ne.symm hr11, Ne.symm hr12,
          Ne.symm hr13, Ne.symm hr14, Ne.symm hr15, Ne.symm hr16]
  · unfold storeByte; simp

/-! ## B8 — `F_unaligned1_setup` (10 instr).

  lw   a5, 0(a4)            -- a5 ← Mem[a4]
  sb   a5, 0(a3)
  srli a1, a5, 8
  sb   a1, 1(a3)
  srli a6, a5, 16
  addi a1, a3, 3
  sb   a6, 2(a3)
  addi a2, a2, -3
  addi a3, a4, 16
  addi a4, zero, 16 -/

def block_F_unaligned1_setup : List Instr :=
  [ Instr.lw   15 14 0
  , Instr.sb   13 15 0
  , Instr.srli 11 15 8
  , Instr.sb   13 11 1
  , Instr.srli 16 15 16
  , Instr.addi 11 13 3
  , Instr.sb   13 16 2
  , Instr.addi 12 12 0xFFFFFFFD
  , Instr.addi 13 14 16
  , Instr.addi 14 0 16
  ]

theorem block_F_unaligned1_setup_triple_composed :
    Triple block_F_unaligned1_setup
      (RComp (fun s s' => s' = advance (setReg s 15 (loadWord s (getReg s 14 + 0))))
        (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 0) (getReg s 15).toUInt8))
          (RComp (fun s s' => s' = advance (setReg s 11 (getReg s 15 >>> 8)))
            (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 1) (getReg s 11).toUInt8))
              (RComp (fun s s' => s' = advance (setReg s 16 (getReg s 15 >>> 16)))
                (RComp (fun s s' => s' = advance (setReg s 11 (getReg s 13 + 3)))
                  (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 2) (getReg s 16).toUInt8))
                    (RComp (fun s s' => s' = advance (setReg s 12 (getReg s 12 + 0xFFFFFFFD)))
                      (RComp (fun s s' => s' = advance (setReg s 13 (getReg s 14 + 16)))
                            (fun s s' => s' = advance (setReg s 14 (getReg s 0 + 16))))))))))))  :=
  (Triple_lw   15 14 0).append <|
  (Triple_sb   13 15 0).append <|
  (Triple_srli 11 15 8).append <|
  (Triple_sb   13 11 1).append <|
  (Triple_srli 16 15 16).append <|
  (Triple_addi 11 13 3).append <|
  (Triple_sb   13 16 2).append <|
  (Triple_addi 12 12 0xFFFFFFFD).append <|
  (Triple_addi 13 14 16).append <|
  (Triple_addi 14 0 16)

def R_block_F_unaligned1_setup : State → State → Prop :=
  fun s s' =>
    let v0 : UInt32 := loadWord s (getReg s 14)
    s'.pc = s.pc + 40 ∧
    getReg s' 11 = getReg s 13 + 3 ∧
    getReg s' 12 = getReg s 12 + 0xFFFFFFFD ∧
    getReg s' 13 = getReg s 14 + 16 ∧
    getReg s' 14 = 16 ∧
    getReg s' 15 = v0 ∧
    getReg s' 16 = v0 >>> 16 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
       r.val ≠ 15 → r.val ≠ 16 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte (storeByte (storeByte s
                (getReg s 13) v0.toUInt8)
                (getReg s 13 + 1) (v0 >>> 8).toUInt8)
                (getReg s 13 + 2) (v0 >>> 16).toUInt8).mem

theorem block_F_unaligned1_setup_triple :
    Triple block_F_unaligned1_setup R_block_F_unaligned1_setup := by
  refine Triple.weaken block_F_unaligned1_setup_triple_composed ?_
  rintro s s'
    ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 40 := by bv_decide
  simp [R_block_F_unaligned1_setup, h_pc]
  refine ⟨?_, ?_⟩
  · intro r hr11 hr12 hr13 hr14 hr15 hr16
    simp [setReg, Ne.symm hr11, Ne.symm hr12,
          Ne.symm hr13, Ne.symm hr14, Ne.symm hr15, Ne.symm hr16]
  · unfold storeByte; simp

end MemcpyProof.Hoare
