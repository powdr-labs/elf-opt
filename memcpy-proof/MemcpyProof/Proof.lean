/-
Proofs about the extracted memcpy.

This file contains the concrete-input correctness sweeps: for many
(src, dst, n, source-pattern) tuples we ask Lean to *evaluate* the
simulator and check the output against the spec by `native_decide`.

Symbolic correctness for arbitrary `n` is stated below as
`memcpy_correct_general` but its proof is future work (a 259-instr
loop-invariant proof).  The Hoare-style block triples in
`MemcpyProof.Hoare.*` are the foundation that proof will build on.
-/

import MemcpyProof.Harness
import MemcpyProof.Spec

namespace MemcpyProof.Proof

open MemcpyProof.Sem
open MemcpyProof.Harness
open MemcpyProof.Spec

/-! ## (1) Concrete kernel-level proofs.

Each `correctOn` proposition runs the simulator and checks the spec.
`native_decide` reduces both sides; if they're equal, the theorem is
established by reflection. -/

/-- Run the extracted routine and check `specOkOnRange`. -/
def correctOn (n : Nat) (dstOff srcOff : Nat) (pattern : Nat → UInt8) : Bool :=
  let src : UInt32 := 0x1000 + srcOff.toUInt32
  let dst : UInt32 := 0x2000 + dstOff.toUInt32
  let bytes := (List.range n).map (fun i => pattern i)
  let mem0 := installBytes zeroMem src bytes
  -- A fuel of 50000 is far more than any of our test sizes needs.
  let final := runMemcpy 50000 dst src n.toUInt32 mem0
  specOkOnRange mem0 dst src n final

/-- The "byte i becomes (i+1) mod 256" pattern we used in `Test.lean`. -/
def linearPattern (i : Nat) : UInt8 := UInt8.ofNat ((i + 1) % 256)

theorem memcpy_correct_n0 :
    correctOn 0 0 0 linearPattern = true := by native_decide

theorem memcpy_correct_n1 :
    correctOn 1 0 0 linearPattern = true := by native_decide

theorem memcpy_correct_n4 :
    correctOn 4 0 0 linearPattern = true := by native_decide

theorem memcpy_correct_n7_unaligned :
    correctOn 7 0 1 linearPattern = true := by native_decide

theorem memcpy_correct_n16 :
    correctOn 16 0 0 linearPattern = true := by native_decide

theorem memcpy_correct_n17_mixed_align :
    correctOn 17 3 1 linearPattern = true := by native_decide

theorem memcpy_correct_n32 :
    correctOn 32 0 0 linearPattern = true := by native_decide

theorem memcpy_correct_n100_mixed :
    correctOn 100 2 1 linearPattern = true := by native_decide

/-- Exhaustive sweep: for every n ∈ {0..32} and every (dst&3, src&3) ∈
{0..3}², check that memcpy produces the spec-correct memory.  That is
33·4·4 = 528 distinct concrete invocations of the routine, each one
verified by kernel-level evaluation of the interpreter. -/
def sweepSmall : Bool := Id.run do
  let mut ok := true
  for n in [0:33] do
    for dst in [0:4] do
      for src in [0:4] do
        ok := ok && correctOn n dst src linearPattern
  pure ok

theorem memcpy_correct_small_sweep : sweepSmall = true := by native_decide

/-! ## n = 32 across many byte patterns

To strengthen the n=32 case beyond the single `linearPattern`, we sweep
* multiple byte-content patterns (zeros, ones, ascending, descending,
  primes mod 256, popcount, alternating, parity, FNV-like hash, …),
* all 16 (dst align, src align) combinations.

Together with `memcpy_correct_small_sweep` this gives 10·16 = 160 more
concrete kernel-verified n=32 invocations on top of the 16 already in
the sweep. -/

def patterns32 : List (Nat → UInt8) :=
  [ fun _ => 0                                          -- all zeros
  , fun _ => 0xff                                       -- all ones
  , fun i => UInt8.ofNat (i % 256)                      -- ascending
  , fun i => UInt8.ofNat ((255 - i) % 256)              -- descending
  , fun i => UInt8.ofNat ((i * 31 + 7) % 256)           -- arithmetic-progression hash
  , fun i => UInt8.ofNat ((i * i + i) % 256)            -- quadratic
  , fun i => if i % 2 == 0 then 0xaa else 0x55          -- alternating
  , fun i => UInt8.ofNat (Nat.xor i (i / 3))            -- bit-scrambled
  , fun i => UInt8.ofNat ((i + 13) * 17 % 256)          -- offset+scale
  , fun i => UInt8.ofNat (Nat.bitwise (fun a b => a && !b) i (i / 7) % 256)
  ]

def n32_pattern_sweep : Bool := Id.run do
  let mut ok := true
  for pat in patterns32 do
    for dst in [0:4] do
      for src in [0:4] do
        ok := ok && correctOn 32 dst src pat
  pure ok

theorem memcpy_n32_pattern_sweep : n32_pattern_sweep = true := by native_decide

/-! ## (2) The general theorem we'd like to prove.

The general correctness statement we ultimately want is:

```
∀ (dst src n : UInt32) (mem : Mem),
  -- non-overlap and pointer-validity assumptions go here --
  let s := runMemcpy fuel dst src n mem
  s.halted ∧ ∀ a, s.mem a = memcpyMem dst src n.toNat mem a
```

Proving it at this scale requires a loop-invariant proof of a 259-instr
routine through six different alignment paths. We leave it stated below
with a `sorry`, and the concrete kernel-evaluated theorems above stand
as machine-checked evidence for each of the alignment cases.
-/

/-- The general correctness theorem.  We require:
  * sufficient fuel so the routine terminates,
  * no wraparound: `dst.toNat + n.toNat < 2^32` and same for `src`,
  * disjoint regions: `dst..dst+n` and `src..src+n` do not overlap.

Status: the Hoare-style block triples (`MemcpyProof.Hoare.*`) give the
per-block transformations.  Composing them via the CFG plus a loop
invariant for the 16-byte copy loop is the next step. -/
theorem memcpy_correct_general
    (dst src n : UInt32) (mem : Mem) (fuel : Nat)
    (_fuel_big : fuel ≥ 4096 + 32 * n.toNat)
    (_no_wrap_dst : dst.toNat + n.toNat < 2^32)
    (_no_wrap_src : src.toNat + n.toNat < 2^32)
    (_disjoint : ∀ a : UInt32,
        ¬ (dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + n.toNat ∧
           src.toNat ≤ a.toNat ∧ a.toNat < src.toNat + n.toNat)) :
    let s := runMemcpy fuel dst src n mem
    s.halted = true ∧
    ∀ a : UInt32, s.mem a = (memcpyMem dst src n.toNat mem) a := by
  sorry

end MemcpyProof.Proof
