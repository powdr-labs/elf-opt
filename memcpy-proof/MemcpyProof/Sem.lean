/-
RV32I small-step semantics.

State:  32 GP registers (forcing x0=0 on read), byte-addressable memory
        as a total function `UInt32 → UInt8`, and a program counter.

We do *not* carry a `halted` flag.  "Routine has returned" is a state
predicate at the harness/CFG layer: `s.pc = retSentinel` for whatever
`retSentinel` was loaded into `ra` on entry.  At the basic-block level
(the Hoare-triple layer) execution is unconditional fold of `exec`.
-/

import MemcpyProof.RV32I

namespace MemcpyProof.Sem

open MemcpyProof.RV32I

/-- Address-indexed bytes. We model RAM as a total function so reads
always succeed; the proofs make no assumption about bytes outside the
region they actually touch. -/
abbrev Mem := UInt32 → UInt8

/-- Register file: exactly 32 GP registers (RISC-V).  Stored as a
`Vector` so updates are flat, not nested-`if` lambdas. -/
abbrev Regs := Vector UInt32 32

export MemcpyProof.RV32I (Reg)

structure State where
  regs : Regs
  mem  : Mem
  pc   : UInt32

@[inline, grind =] def getReg (s : State) (r : Reg) : UInt32 :=
  if r = 0 then 0 else s.regs[r]

@[inline, grind =] def setReg (s : State) (r : Reg) (v : UInt32) : State :=
  if r = 0 then s
  else { s with regs := s.regs.set r.val v r.isLt }

@[inline, grind =] def loadByte (s : State) (addr : UInt32) : UInt8 := s.mem addr

@[inline, grind =] def storeByte (s : State) (addr : UInt32) (b : UInt8) : State :=
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
  { s with pc := target }

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

/-- One step.  Stops at `haltAt`: when `s.pc = haltAt`, the routine has
returned and we leave the state alone.  This is the harness's
termination criterion, *not* a state field. -/
@[inline] def step (code : CodeFn) (haltAt : UInt32) (s : State) : State :=
  if s.pc = haltAt then s else exec s (decode (code s.pc))

def run (code : CodeFn) (haltAt : UInt32) : Nat → State → State
  | 0, s     => s
  | n+1, s   => if s.pc = haltAt then s else run code haltAt n (step code haltAt s)

@[simp] theorem run_zero (code : CodeFn) (haltAt : UInt32) (s : State) :
    run code haltAt 0 s = s := rfl

theorem run_done (code : CodeFn) (haltAt : UInt32) (s : State) (n : Nat)
    (h : s.pc = haltAt) :
    run code haltAt n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, h]

/-- Unfold one step of `run` when we have not yet reached `haltAt`. -/
theorem run_succ (code : CodeFn) (haltAt : UInt32) (s : State)
    (h : s.pc ≠ haltAt) (n : Nat) :
    run code haltAt (n+1) s = run code haltAt n (step code haltAt s) := by
  show (if s.pc = haltAt then s else run code haltAt n (step code haltAt s))
       = run code haltAt n (step code haltAt s)
  rw [if_neg h]

/-- `run` composes over Nat addition. -/
theorem run_add (code : CodeFn) (haltAt : UInt32) (a b : Nat) (s : State) :
    run code haltAt (a + b) s = run code haltAt b (run code haltAt a s) := by
  induction a generalizing s with
  | zero => show run code haltAt (0 + b) s = run code haltAt b (run code haltAt 0 s); simp
  | succ a ih =>
    show run code haltAt (a + 1 + b) s = run code haltAt b (run code haltAt (a + 1) s)
    rw [show a + 1 + b = (a + b) + 1 from by omega]
    show (if s.pc = haltAt then s else run code haltAt (a + b) (step code haltAt s))
        = run code haltAt b (if s.pc = haltAt then s else run code haltAt a (step code haltAt s))
    by_cases h : s.pc = haltAt
    · simp [h, run_done _ _ _ _ h]
    · simp [h]; exact ih (step code haltAt s)

end MemcpyProof.Sem
