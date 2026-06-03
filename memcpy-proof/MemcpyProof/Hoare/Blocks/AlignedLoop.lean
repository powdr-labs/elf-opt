/-
The aligned 16-byte main copy loop body — B13 / B14.

B14 (11 instr, PCs 0x200a1c..0x200a44): pure loop body.
B13 (12 instr, PCs 0x200a18..0x200a44): preamble + B14.

The 11-instr body's Triple typechecks too slowly when proved as a single
chain (the whnf budget blows on the deeply-nested RComp).  We split it
into two halves (5 lw/sw + 6 sw/addi) and combine.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Half 1 (5 instr): 4 word-loads + the first sw. -/

private def block_F_iter_h1 : List Instr :=
  [ Instr.lw 15 14 0
  , Instr.lw 16 14 4
  , Instr.lw 17 14 8
  , Instr.lw  5 14 12
  , Instr.sw 13 15 0
  ]

private theorem block_F_iter_h1_triple_composed :
    Triple block_F_iter_h1
      (RComp (fun s s' => s' = advance (setReg s 15 (loadWord s (getReg s 14 + 0))))
        (RComp (fun s s' => s' = advance (setReg s 16 (loadWord s (getReg s 14 + 4))))
          (RComp (fun s s' => s' = advance (setReg s 17 (loadWord s (getReg s 14 + 8))))
            (RComp (fun s s' => s' = advance (setReg s 5 (loadWord s (getReg s 14 + 12))))
                  (fun s s' => s' = advance (storeWord s (getReg s 13 + 0) (getReg s 15)))))))  :=
  (Triple_lw 15 14 0).append <|
  (Triple_lw 16 14 4).append <|
  (Triple_lw 17 14 8).append <|
  (Triple_lw  5 14 12).append <|
  (Triple_sw 13 15 0)

private def R_h1 : State → State → Prop :=
  fun s s' =>
    let a4 := getReg s 14
    let w0 := loadWord s a4
    let w1 := loadWord s (a4 + 4)
    let w2 := loadWord s (a4 + 8)
    let w3 := loadWord s (a4 + 12)
    s'.pc = s.pc + 20 ∧
    getReg s' 13 = getReg s 13 ∧
    getReg s' 14 = a4 ∧
    getReg s' 15 = w0 ∧
    getReg s' 16 = w1 ∧
    getReg s' 17 = w2 ∧
    getReg s'  5 = w3 ∧
    (∀ r : Fin 32, r.val ≠ 5 → r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord s (getReg s 13) w0).mem

private theorem block_F_iter_h1_triple : Triple block_F_iter_h1 R_h1 := by
  refine Triple.weaken block_F_iter_h1_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_h1, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h5' h15' h16' h17'
    simp [setReg, Ne.symm h5', Ne.symm h15', Ne.symm h16', Ne.symm h17']
  · unfold storeWord; simp [storeByte]

/-! ## Half 2 (6 instr): 3 word-stores + 3 pointer-bumps. -/

private def block_F_iter_h2 : List Instr :=
  [ Instr.sw   13 16 4
  , Instr.sw   13 17 8
  , Instr.sw   13  5 12
  , Instr.addi 14 14 16
  , Instr.addi 12 12 0xFFFFFFF0
  , Instr.addi 13 13 16
  ]

private theorem block_F_iter_h2_triple_composed :
    Triple block_F_iter_h2
      (RComp (fun s s' => s' = advance (storeWord s (getReg s 13 + 4) (getReg s 16)))
        (RComp (fun s s' => s' = advance (storeWord s (getReg s 13 + 8) (getReg s 17)))
          (RComp (fun s s' => s' = advance (storeWord s (getReg s 13 + 12) (getReg s 5)))
            (RComp (fun s s' => s' = advance (setReg s 14 (getReg s 14 + 16)))
              (RComp (fun s s' => s' = advance (setReg s 12 (getReg s 12 + 0xFFFFFFF0)))
                    (fun s s' => s' = advance (setReg s 13 (getReg s 13 + 16)))))))) :=
  (Triple_sw   13 16 4).append <|
  (Triple_sw   13 17 8).append <|
  (Triple_sw   13  5 12).append <|
  (Triple_addi 14 14 16).append <|
  (Triple_addi 12 12 0xFFFFFFF0).append <|
  (Triple_addi 13 13 16)

private def R_h2 : State → State → Prop :=
  fun s s' =>
    let a3 := getReg s 13
    s'.pc = s.pc + 24 ∧
    getReg s' 12 = getReg s 12 + 0xFFFFFFF0 ∧
    getReg s' 13 = a3 + 16 ∧
    getReg s' 14 = getReg s 14 + 16 ∧
    getReg s' 15 = getReg s 15 ∧
    getReg s' 16 = getReg s 16 ∧
    getReg s' 17 = getReg s 17 ∧
    getReg s'  5 = getReg s 5 ∧
    (∀ r : Fin 32, r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord (storeWord (storeWord s
                (a3 + 4) (getReg s 16))
                (a3 + 8) (getReg s 17))
                (a3 + 12) (getReg s 5)).mem

private theorem block_F_iter_h2_triple : Triple block_F_iter_h2 R_h2 := by
  refine Triple.weaken block_F_iter_h2_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 24 := by bv_decide
  simp [R_h2, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h12 h13 h14
    simp [setReg, Ne.symm h12, Ne.symm h13, Ne.symm h14]
  · unfold storeWord; simp [storeByte]

/-! ## B14 — assembled from the two halves. -/

def block_F_iter : List Instr := block_F_iter_h1 ++ block_F_iter_h2

theorem block_F_iter_triple_composed :
    Triple block_F_iter (RComp R_h1 R_h2) :=
  block_F_iter_h1_triple.append block_F_iter_h2_triple

/-! ## B13 — preamble (1 instr) + B14 (11 instr). -/

def block_F_first : List Instr := Instr.addi 11 0 15 :: block_F_iter

theorem block_F_first_triple_composed :
    Triple block_F_first
      (RComp (fun s s' => s' = advance (setReg s 11 (getReg s 0 + 15)))
             (RComp R_h1 R_h2)) :=
  (Triple_addi 11 0 15).append block_F_iter_triple_composed

end MemcpyProof.Hoare
