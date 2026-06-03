/-
The "trivial" memcpy basic blocks — those of 1 or 2 instructions, all
straight-line, that each terminate at the *following* branch instruction.

Each 1-instr block's `Triple` is literally the corresponding per-instruction
`Triple_…` lemma; nothing more to do.  The 2-instr blocks (B25, B37, B39)
need one `Triple.append` plus a small `weaken`.

Block IDs reference `BLOCKS.md`.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## 1-instruction blocks. -/

-- B3 @ 0x00200948 : andi a1, a3, 3
def block_B3 : List Instr := [Instr.andi 11 13 3]
theorem block_B3_triple :
    Triple block_B3 (fun s s' => s' = advance (setReg s 11 (getReg s 13 &&& 3))) :=
  Triple_andi 11 13 3

-- B4 @ 0x00200950 : addi a5, zero, 32
def block_B4 : List Instr := [Instr.addi 15 0 32]
theorem block_B4_triple :
    Triple block_B4 (fun s s' => s' = advance (setReg s 15 32)) := fun _ => rfl

-- B5 @ 0x00200958 : addi a5, zero, 3
def block_B5 : List Instr := [Instr.addi 15 0 3]
theorem block_B5_triple :
    Triple block_B5 (fun s s' => s' = advance (setReg s 15 3)) := fun _ => rfl

-- B6 @ 0x00200960 : addi a5, zero, 2
def block_B6 : List Instr := [Instr.addi 15 0 2]
theorem block_B6_triple :
    Triple block_B6 (fun s s' => s' = advance (setReg s 15 2)) := fun _ => rfl

-- B7 @ 0x00200968 : addi a5, zero, 1
def block_B7 : List Instr := [Instr.addi 15 0 1]
theorem block_B7_triple :
    Triple block_B7 (fun s s' => s' = advance (setReg s 15 1)) := fun _ => rfl

-- B12 @ 0x00200a10 : addi a1, zero, 16
def block_B12 : List Instr := [Instr.addi 11 0 16]
theorem block_B12_triple :
    Triple block_B12 (fun s s' => s' = advance (setReg s 11 16)) := fun _ => rfl

-- B15 @ 0x00200a4c : andi a1, a2, 8
def block_B15 : List Instr := [Instr.andi 11 12 8]
theorem block_B15_triple :
    Triple block_B15 (fun s s' => s' = advance (setReg s 11 (getReg s 12 &&& 8))) :=
  Triple_andi 11 12 8

-- B17 @ 0x00200a6c : andi a1, a2, 4
def block_B17 : List Instr := [Instr.andi 11 12 4]
theorem block_B17_triple :
    Triple block_B17 (fun s s' => s' = advance (setReg s 11 (getReg s 12 &&& 4))) :=
  Triple_andi 11 12 4

-- B26 @ 0x00200b98 : andi a1, a2, 8
def block_B26 : List Instr := [Instr.andi 11 12 8]
theorem block_B26_triple :
    Triple block_B26 (fun s s' => s' = advance (setReg s 11 (getReg s 12 &&& 8))) :=
  Triple_andi 11 12 8

-- B27 @ 0x00200ba0 : andi a1, a2, 4
def block_B27 : List Instr := [Instr.andi 11 12 4]
theorem block_B27_triple :
    Triple block_B27 (fun s s' => s' = advance (setReg s 11 (getReg s 12 &&& 4))) :=
  Triple_andi 11 12 4

-- B29 @ 0x00200bd4 : andi a1, a2, 2
def block_B29 : List Instr := [Instr.andi 11 12 2]
theorem block_B29_triple :
    Triple block_B29 (fun s s' => s' = advance (setReg s 11 (getReg s 12 &&& 2))) :=
  Triple_andi 11 12 2

-- B30 @ 0x00200bdc : andi a1, a2, 1
def block_B30 : List Instr := [Instr.andi 11 12 1]
theorem block_B30_triple :
    Triple block_B30 (fun s s' => s' = advance (setReg s 11 (getReg s 12 &&& 1))) :=
  Triple_andi 11 12 1

-- B33 @ 0x00200c04 : andi a1, a2, 1
def block_B33 : List Instr := [Instr.andi 11 12 1]
theorem block_B33_triple :
    Triple block_B33 (fun s s' => s' = advance (setReg s 11 (getReg s 12 &&& 1))) :=
  Triple_andi 11 12 1

/-! ## 2-instruction "dispatch" blocks B25 / B37 / B39. -/

private def mkBlock_dispatch (K : UInt32) : List Instr :=
  [ Instr.addi 13 11 0
  , Instr.andi 11 12 K
  ]

private def R_dispatch (K : UInt32) : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 8 ∧
    getReg s' 13 = getReg s 11 ∧
    getReg s' 11 = getReg s 12 &&& K ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 13 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

private theorem Triple_dispatch (K : UInt32) :
    Triple (mkBlock_dispatch K) (R_dispatch K) := by
  refine Triple.weaken
    ((Triple_addi 13 11 0).append (Triple_andi 11 12 K)) ?_
  rintro s s' ⟨_, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 = s.pc + 8 := by bv_decide
  simp [R_dispatch, h_pc]
  intro r hr11 hr13
  simp [setReg, Ne.symm hr11, Ne.symm hr13]

def block_B25 := mkBlock_dispatch 16
theorem block_B25_triple : Triple block_B25 (R_dispatch 16) := Triple_dispatch 16

def block_B37 := mkBlock_dispatch 8
theorem block_B37_triple : Triple block_B37 (R_dispatch 8) := Triple_dispatch 8

def block_B39 := mkBlock_dispatch 4
theorem block_B39_triple : Triple block_B39 (R_dispatch 4) := Triple_dispatch 4

/-! ## 1-instr `addi` blocks with negative immediates (loop epilogues). -/

-- B10 @ 0x2009f8 : addi a4, a3, -13
def block_B10 : List Instr := [Instr.addi 14 13 0xFFFFFFF3]
theorem block_B10_triple :
    Triple block_B10
      (fun s s' => s' = advance (setReg s 14 (getReg s 13 + 0xFFFFFFF3))) :=
  Triple_addi 14 13 0xFFFFFFF3

-- B21 @ 0x200b00 : addi a4, a3, -15
def block_B21 : List Instr := [Instr.addi 14 13 0xFFFFFFF1]
theorem block_B21_triple :
    Triple block_B21
      (fun s s' => s' = advance (setReg s 14 (getReg s 13 + 0xFFFFFFF1))) :=
  Triple_addi 14 13 0xFFFFFFF1

-- B24 @ 0x200b88 : addi a4, a3, -14
def block_B24 : List Instr := [Instr.addi 14 13 0xFFFFFFF2]
theorem block_B24_triple :
    Triple block_B24
      (fun s s' => s' = advance (setReg s 14 (getReg s 13 + 0xFFFFFFF2))) :=
  Triple_addi 14 13 0xFFFFFFF2

/-! ## Jumps and returns. -/

-- B40 @ 0x200d00 : jal zero, -300  (unconditional jump to 0x200bd4)
def block_B40 : List Instr := [Instr.jal 0 0xFFFFFED4]
theorem block_B40_triple :
    Triple block_B40
      (fun s s' => s' = jumpTo (setReg s 0 (s.pc + 4)) (s.pc + 0xFFFFFED4)) :=
  Triple_jal 0 0xFFFFFED4

-- B31 / B35 @ 0x200be4 / 0x200c14 : jalr zero, 0(ra)  (return)
def block_ret : List Instr := [Instr.jalr 0 1 0]
theorem block_ret_triple :
    Triple block_ret
      (fun s s' => s' = jumpTo (setReg s 0 (s.pc + 4))
                          ((getReg s 1 + 0) &&& (~~~ 1))) :=
  Triple_jalr 0 1 0

end MemcpyProof.Hoare
