/-
RV32I small-step semantics.

State:  32 GP registers (forcing x0=0 on read), byte-addressable memory
        as a total function `UInt32 → UInt8`, program counter, and a
        `halted` flag (set when `pc` equals the saved return address
        on entry — i.e. `ret` has been executed).
-/

import MemcpyProof.RV32I

namespace MemcpyProof.Sem

open MemcpyProof.RV32I

/-- Address-indexed bytes. We model RAM as a total function so reads
always succeed; the proofs make no assumption about bytes outside the
region they actually touch. -/
abbrev Mem := UInt32 → UInt8

/-- Register file. Reads from x0 must return 0; we enforce that in
`getReg` rather than in the underlying function so update logic stays
uniform. -/
abbrev Regs := UInt32 → UInt32

structure State where
  regs   : Regs
  mem    : Mem
  pc     : UInt32
  /-- Set to true once execution returns from the routine — i.e. when
  control transfers back to the `ra` value that was set on entry. -/
  halted : Bool
  /-- The return address we entered with; once `pc = haltAt`, we stop. -/
  haltAt : UInt32

@[inline] def getReg (s : State) (r : UInt32) : UInt32 :=
  if r == 0 then 0 else s.regs r

@[inline] def setReg (s : State) (r : UInt32) (v : UInt32) : State :=
  if r == 0 then s
  else { s with regs := fun i => if i == r then v else s.regs i }

@[inline] def loadByte (s : State) (addr : UInt32) : UInt8 := s.mem addr

@[inline] def storeByte (s : State) (addr : UInt32) (b : UInt8) : State :=
  { s with mem := fun a => if a == addr then b else s.mem a }

def loadHalf (s : State) (addr : UInt32) : UInt32 :=
  let b0 := (loadByte s addr).toUInt32
  let b1 := (loadByte s (addr + 1)).toUInt32
  b0 ||| (b1 <<< 8)

def loadWord (s : State) (addr : UInt32) : UInt32 :=
  let b0 := (loadByte s addr).toUInt32
  let b1 := (loadByte s (addr + 1)).toUInt32
  let b2 := (loadByte s (addr + 2)).toUInt32
  let b3 := (loadByte s (addr + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

def storeHalf (s : State) (addr : UInt32) (v : UInt32) : State :=
  let s1 := storeByte s addr (v.toUInt8)
  storeByte s1 (addr + 1) ((v >>> 8).toUInt8)

def storeWord (s : State) (addr : UInt32) (v : UInt32) : State :=
  let s1 := storeByte s addr (v.toUInt8)
  let s2 := storeByte s1 (addr + 1) ((v >>> 8).toUInt8)
  let s3 := storeByte s2 (addr + 2) ((v >>> 16).toUInt8)
  storeByte s3 (addr + 3) ((v >>> 24).toUInt8)

@[inline] def signedLT (a b : UInt32) : Bool :=
  ((a + 0x80000000) < (b + 0x80000000))

@[inline] def signedGE (a b : UInt32) : Bool := !(signedLT a b)

@[reducible] def advance (s : State) : State :=
  { s with pc := s.pc + 4 }

@[reducible] def jumpTo (s : State) (target : UInt32) : State :=
  if target == s.haltAt then { s with pc := target, halted := true }
  else { s with pc := target }

@[reducible] def exec (s : State) (i : Instr) : State :=
  match i with
  -- op-imm
  | .addi  d a imm => advance (setReg s d (getReg s a + imm))
  | .slti  d a imm => advance (setReg s d (if signedLT (getReg s a) imm then 1 else 0))
  | .sltiu d a imm => advance (setReg s d (if getReg s a < imm then 1 else 0))
  | .xori  d a imm => advance (setReg s d (getReg s a ^^^ imm))
  | .ori   d a imm => advance (setReg s d (getReg s a ||| imm))
  | .andi  d a imm => advance (setReg s d (getReg s a &&& imm))
  | .slli  d a sh  => advance (setReg s d (getReg s a <<< sh))
  | .srli  d a sh  => advance (setReg s d (getReg s a >>> sh))
  | .srai  d a sh  =>
    let v := getReg s a
    let r := v >>> sh
    let signMask : UInt32 :=
      if v &&& 0x80000000 != 0 then
        ((1 <<< sh) - 1) <<< (32 - sh)
      else 0
    advance (setReg s d (r ||| signMask))
  -- R-type
  | .add  d a b => advance (setReg s d (getReg s a + getReg s b))
  | .sub  d a b => advance (setReg s d (getReg s a - getReg s b))
  | .sll  d a b => advance (setReg s d (getReg s a <<< (getReg s b &&& 0x1f)))
  | .slt  d a b => advance (setReg s d (if signedLT (getReg s a) (getReg s b) then 1 else 0))
  | .sltu d a b => advance (setReg s d (if getReg s a < getReg s b then 1 else 0))
  | .xor  d a b => advance (setReg s d (getReg s a ^^^ getReg s b))
  | .srl  d a b => advance (setReg s d (getReg s a >>> (getReg s b &&& 0x1f)))
  | .sra  d a b =>
    let v := getReg s a
    let sh := getReg s b &&& 0x1f
    let r := v >>> sh
    let signMask : UInt32 :=
      if v &&& 0x80000000 != 0 then
        ((1 <<< sh) - 1) <<< (32 - sh)
      else 0
    advance (setReg s d (r ||| signMask))
  | .or_  d a b => advance (setReg s d (getReg s a ||| getReg s b))
  | .and_ d a b => advance (setReg s d (getReg s a &&& getReg s b))
  | .mul  d a b => advance (setReg s d (getReg s a * getReg s b))
  -- loads
  | .lb  d a imm =>
    let addr := getReg s a + imm
    let b := loadByte s addr
    advance (setReg s d (signExt b.toUInt32 7))
  | .lh  d a imm =>
    let addr := getReg s a + imm
    advance (setReg s d (signExt (loadHalf s addr) 15))
  | .lw  d a imm =>
    let addr := getReg s a + imm
    advance (setReg s d (loadWord s addr))
  | .lbu d a imm =>
    let addr := getReg s a + imm
    advance (setReg s d (loadByte s addr).toUInt32)
  | .lhu d a imm =>
    let addr := getReg s a + imm
    advance (setReg s d (loadHalf s addr))
  -- stores
  | .sb a b imm =>
    let addr := getReg s a + imm
    advance (storeByte s addr (getReg s b).toUInt8)
  | .sh a b imm =>
    let addr := getReg s a + imm
    advance (storeHalf s addr (getReg s b))
  | .sw a b imm =>
    let addr := getReg s a + imm
    advance (storeWord s addr (getReg s b))
  -- branches
  | .beq  a b imm =>
    if getReg s a == getReg s b then jumpTo s (s.pc + imm) else advance s
  | .bne  a b imm =>
    if getReg s a != getReg s b then jumpTo s (s.pc + imm) else advance s
  | .blt  a b imm =>
    if signedLT (getReg s a) (getReg s b) then jumpTo s (s.pc + imm) else advance s
  | .bge  a b imm =>
    if signedGE (getReg s a) (getReg s b) then jumpTo s (s.pc + imm) else advance s
  | .bltu a b imm =>
    if getReg s a < getReg s b then jumpTo s (s.pc + imm) else advance s
  | .bgeu a b imm =>
    if getReg s a ≥ getReg s b then jumpTo s (s.pc + imm) else advance s
  -- jumps + upper-imm
  | .jal  d imm =>
    let s' := setReg s d (s.pc + 4)
    jumpTo s' (s.pc + imm)
  | .jalr d a imm =>
    let target := (getReg s a + imm) &&& (~~~ 1)
    let s' := setReg s d (s.pc + 4)
    jumpTo s' target
  | .lui   d imm => advance (setReg s d imm)
  | .auipc d imm => advance (setReg s d (s.pc + imm))
  | .other _ => advance s   -- treat unknown as no-op; should not happen in proof region

/-- Instruction fetch from a code-region: returns the encoded word at PC,
or 0 outside the routine's range. -/
abbrev CodeFn := UInt32 → UInt32

@[inline] def step (code : CodeFn) (s : State) : State :=
  if s.halted then s else exec s (decode (code s.pc))

def run (code : CodeFn) : Nat → State → State
  | 0, s     => s
  | n+1, s   => if s.halted then s else run code n (step code s)

@[simp] theorem run_zero (code : CodeFn) (s : State) : run code 0 s = s := rfl

theorem run_halted (code : CodeFn) (s : State) (n : Nat) (h : s.halted = true) :
    run code n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, h]

/-- Unfold one step of `run` when the state is not halted. -/
theorem run_succ (code : CodeFn) (s : State) (h : s.halted = false) (n : Nat) :
    run code (n+1) s = run code n (step code s) := by
  show (if s.halted = true then s else run code n (step code s)) = run code n (step code s)
  rw [h]; rfl

/-- `run` composes over Nat addition. -/
theorem run_add (code : CodeFn) (a b : Nat) (s : State) :
    run code (a + b) s = run code b (run code a s) := by
  induction a generalizing s with
  | zero => show run code (0 + b) s = run code b (run code 0 s); simp
  | succ a ih =>
    show run code (a + 1 + b) s = run code b (run code (a + 1) s)
    rw [show a + 1 + b = (a + b) + 1 from by omega]
    show (if s.halted = true then s else run code (a + b) (step code s))
        = run code b (if s.halted = true then s else run code a (step code s))
    by_cases h : s.halted = true
    · simp [h, run_halted _ _ _ h]
    · simp [h]; exact ih (step code s)

end MemcpyProof.Sem
