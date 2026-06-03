/- Runtime test: load the ELF, run memcpy(dst, src, n) on the simulator,
   and compare the output bytes to the expected source bytes.

   This is *not* a proof — it's a sanity check that our decoder + interpreter
   match real RV32 hardware semantics before we ask Lean to verify them. -/

import MemcpyProof.Harness
import MemcpyProof.RV32I

open MemcpyProof.Sem
open MemcpyProof.Harness
open MemcpyProof.Extract

def runOne (n : Nat) (srcAlign dstAlign : Nat) : IO Unit := do
  let src : UInt32 := 0x1000 + srcAlign.toUInt32
  let dst : UInt32 := 0x2000 + dstAlign.toUInt32
  -- Source pattern: byte i = (i+1) mod 256.
  let srcBytes := (List.range n).map (fun i => UInt8.ofNat ((i + 1) % 256))
  let mem := installBytes zeroMem src srcBytes
  let final := runMemcpy 200000 dst src n.toUInt32 mem
  let got := readBytes final.mem dst n
  let ok := got == srcBytes
  IO.println s!"n={n} src+{srcAlign} dst+{dstAlign} -> returned={hasReturned final} steps≤200000 ok={ok}"
  if !ok then
    IO.println s!"  expected: {srcBytes}"
    IO.println s!"  got     : {got}"

def main : IO UInt32 := do
  for (n, sa, da) in [(0,0,0), (1,0,0), (4,0,0), (7,1,0), (8,0,0), (15,3,2), (16,0,0),
                       (17,1,3), (31,2,1), (32,0,0), (64,3,3), (100,1,2)] do
    runOne n sa da
  return 0
