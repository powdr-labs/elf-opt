/-
Test harness around the RV32I interpreter: a `runMemcpy` that loads the
extracted code, sets up registers, and steps until either the routine
returns or a step budget is exhausted.
-/

import MemcpyProof.Sem
import MemcpyProof.Extract

namespace MemcpyProof.Harness

open MemcpyProof.Sem
open MemcpyProof.Extract

/-- Decode the instruction at absolute PC `pc` using the extracted code.
We use the auto-generated `code` `match` for proof-friendly reduction:
the kernel can compute `code <literal>` straight to the encoded word. -/
@[reducible] def memcpyCode (pc : UInt32) : UInt32 := code pc

/-- Sentinel return address; on `ret` the interpreter stops. Must not lie
inside the routine [vaddr, vaddr + 4*numInstrs). Kept even so the `&~1`
mask applied by `jalr` doesn't shift it. -/
def retSentinel : UInt32 := 0xdead_beee

/-- Empty register file (all zeroed). -/
def zeroRegs : Regs := fun _ => 0

/-- Empty memory (all zeroed). The proof state can override this. -/
def zeroMem : Mem := fun _ => 0

/-- Initial state for invoking memcpy(dst, src, n). -/
def initial (dst src n : UInt32) (mem : Mem) : State :=
  let r0 : Regs := fun _ => 0
  -- RISC-V calling convention: a0,a1,a2 in x10,x11,x12; ra is x1.
  let r1 : Regs := fun i =>
    if i == 1  then retSentinel
    else if i == 10 then dst
    else if i == 11 then src
    else if i == 12 then n
    else r0 i
  { regs := r1, mem := mem, pc := vaddr, halted := false, haltAt := retSentinel }

/-- Run up to `fuel` steps. -/
def runMemcpy (fuel : Nat) (dst src n : UInt32) (mem : Mem) : State :=
  run memcpyCode fuel (initial dst src n mem)

/-- Convenience: install a list of bytes at `base..base+len` in memory. -/
def installBytes (mem : Mem) (base : UInt32) (bs : List UInt8) : Mem :=
  let rec go (m : Mem) (a : UInt32) : List UInt8 → Mem
    | [] => m
    | b :: bs => go (fun x => if x == a then b else m x) (a + 1) bs
  go mem base bs

/-- Read `len` bytes from memory starting at `base`. -/
def readBytes (mem : Mem) (base : UInt32) : Nat → List UInt8
  | 0     => []
  | n + 1 => mem base :: readBytes mem (base + 1) n

end MemcpyProof.Harness
