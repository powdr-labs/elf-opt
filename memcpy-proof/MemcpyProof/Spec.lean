/-
Specification of memcpy.

  `memcpy(dst, src, n)` copies the `n` bytes starting at `src` to the
  buffer at `dst`. Bytes outside `[dst, dst+n)` are unchanged. We model
  no aliasing/overlap guarantees here; the test cases pick disjoint
  regions, which is what C's memcpy semantically requires.
-/

import MemcpyProof.Sem

namespace MemcpyProof.Spec

open MemcpyProof.Sem

/-- Pure spec: copy `n` bytes from `src` to `dst` inside `mem`. -/
def memcpyMem (dst src : UInt32) : Nat → Mem → Mem
  | 0,     m => m
  | k + 1, m =>
    let m' := fun a => if a == dst then m src else m a
    memcpyMem (dst + 1) (src + 1) k m'

/-- A state `s` "looks like" a successful memcpy invocation finishing —
i.e. it halted, and its memory matches the spec. -/
def specOk (initMem : Mem) (dst src : UInt32) (n : Nat) (final : State) : Prop :=
  final.halted = true ∧ ∀ a : UInt32, final.mem a = (memcpyMem dst src n initMem) a

/-- Decidable variant for `native_decide` proofs: only compare bytes over
the finite copy region. -/
def specOkOnRange (initMem : Mem) (dst src : UInt32) (n : Nat) (final : State) : Bool :=
  let rec checkRange (i : Nat) : Bool :=
    match i with
    | 0     => true
    | k + 1 =>
      let a := dst + (n - i).toUInt32
      (final.mem a == (memcpyMem dst src n initMem) a) && checkRange k
  final.halted && checkRange n

end MemcpyProof.Spec
