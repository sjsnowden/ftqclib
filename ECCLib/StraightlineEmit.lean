/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.StraightlineGate

set_option linter.unusedSectionVars false

/-!
# Emission: verified straightline programs as structural Verilog

The output end of the gate stack. A signature-generic printer takes any `Prog C U B n` to a
flat structural Verilog module: one `assign` per SSA line, so the emitted text carries the
shared gate count visibly (37 / 202 operator assigns), and `wfb` makes the listing
topologically ordered as written. A companion printer emits a self-checking testbench
whose expected vectors are computed in Lean by `Prog.run`, for an independent check in an
external simulator.

**The trust boundary, stated**: emission is deliberately UNVERIFIED. Every theorem
lives on the Lean side (`compileNet_run`, `compileNet_gates_le`, `compileProg_nodup`,
`compileProg_depth`); the printed text is an interface artifact, and the testbench is
the cross-system check that the boundary was crossed faithfully. SSA form means the
printer needs no parenthesizer: every operand is atomic (a port bit, a literal, or a
wire), so precedence bugs are structurally impossible.

**The GF(256) bridge**: emitting the big multiplier requires *running* the compiler,
and the Pi-form `tbl r8` is exponentially slow in the interpreter. `tbl8M`
materializes the power table as list levels; the kernel theorem `tbl8M_eq` (5.5k
heartbeats — the kernel amortizes the table across all 512 entries) and
`gf256Prog_eq_certified` tie the emitted object to the certified tree, so the
artifact's provenance is a theorem, not a convention.

Writing the printed text to files is left to a separate runner, so that `#eval` and
`IO.FS.writeFile` stay out of certified files.
-/

namespace ECCLib

open SLP

/-! ## The materialized GF(256) table, certified against the Pi-form -/

/-- One shift-and-reduce step on a materialized coordinate list (m = 7, 8 coords). -/
def xtimeL (r : List (ZMod 2)) (v : List (ZMod 2)) : List (ZMod 2) :=
  let last := v.getD 7 0
  (List.range 8).map (fun k =>
    (if k = 0 then 0 else v.getD (k - 1) 0) + last * r.getD k 0)

/-- The AES reduction word, as a list. -/
def r8List : List (ZMod 2) := List.ofFn (fun k : Fin 8 => r8 k)

/-- Power levels `α⁰ … αⁿ`, each computed from the PREVIOUS materialized level — linear,
never through the exponential Pi-form chain. -/
def powLevels : ℕ → List (List (ZMod 2))
  | 0 => [(List.range 8).map (fun k => if k = 0 then 1 else 0)]
  | n + 1 =>
    let a := powLevels n
    a ++ [xtimeL r8List (a.getD n [])]

/-- The materialized GF(256) multiplication table (levels 0..14 cover `i + j`). -/
def tbl8L : List (List (ZMod 2)) := powLevels 14

/-- The materialized table, in the Pi shape the netlist builder consumes. -/
def tbl8M (i j k : Fin 8) : ZMod 2 := (tbl8L.getD ((i : ℕ) + (j : ℕ)) []).getD (k : ℕ) 0

/-- **The bridge**: the materialized table IS the certified Pi-form table — all 512
entries, in the kernel (measured 5.5k heartbeats; the kernel shares the level
computation across entries). -/
theorem tbl8M_eq : ∀ i j k : Fin 8, tbl8M i j k = tbl r8 i j k := by decide

/-! ## The compiled flagship programs -/

/-- The compiled GF(16) multiplier: 37 shared lines from the certified 105-gate tree. -/
def gf16Prog : Prog Bool BoolUn BoolBin 8 :=
  compileNet (Circuit.cfoldVec (Circuit.bilinNet (fun i j k => tbl r4 i j k)))

/-- The compiled GF(256) multiplier, built through the materialized table: 202 shared
lines. `gf256Prog_eq_certified` ties it to the certified tree. -/
def gf256Prog : Prog Bool BoolUn BoolBin 16 :=
  compileNet (Circuit.cfoldVec (Circuit.bilinNet (fun i j k => tbl8M i j k)))

/-- The emitted GF(256) program IS the certified tree's compile — provenance by
theorem. -/
theorem gf256Prog_eq_certified :
    gf256Prog = compileNet (Circuit.cfoldVec (Circuit.bilinNet (fun i j k => tbl r8 i j k))) := by
  have h : (fun i j k => tbl8M i j k) = (fun i j k => tbl r8 i j k) := by
    funext i j k
    exact tbl8M_eq i j k
  unfold gf256Prog
  rw [h]

/-! ## The printer -/

/-- Everything the printer needs about a signature and a module: names, port
declarations, and the operator tables. Emitting a new signature or module costs exactly
one of these records. -/
structure EmitCfg (C U B : Type*) where
  moduleName : String
  /-- Port declarations, one per line, no trailing commas. -/
  portDecls : List String
  /-- Input operand `inp i` as a Verilog expression. -/
  inputName : ℕ → String
  /-- Output slot `k` as a Verilog lvalue. -/
  outputName : ℕ → String
  cstStr : C → String
  unOp : U → String
  binOp : B → String
  /-- Provenance comment lines (source term, theorems, measurements). -/
  header : List String

variable {C U B : Type*}

/-- An operand is always ATOMIC in Verilog terms — the reason no parenthesizer exists. -/
def argStr (cfg : EmitCfg C U B) : Arg C n → String
  | .inp i => cfg.inputName (i : ℕ)
  | .cst c => cfg.cstStr c
  | .reg k => s!"r{k}"

def instrStr (cfg : EmitCfg C U B) : Instr C U B n → String
  | .un o a => s!"{cfg.unOp o}{argStr cfg a}"
  | .bin o a b => s!"{argStr cfg a} {cfg.binOp o} {argStr cfg b}"

/-- The module text: header comments, ports, chunked wire declarations, one `assign`
per SSA line, output assigns. Gate count = operator-assign count = `P.lines.length`. -/
def emitVerilog (cfg : EmitCfg C U B) (P : Prog C U B n) : String :=
  let len := P.lines.length
  let hdr := cfg.header.map (fun l => s!"// {l}")
  let ports := match cfg.portDecls with
    | [] => []
    | ps => [String.intercalate ",\n" (ps.map (fun p => s!"  {p}"))]
  let wireDecls := (List.range ((len + 7) / 8)).map (fun c =>
    let ws := (List.range 8).filterMap (fun j =>
      let idx := c * 8 + j
      if idx < len then some s!"r{idx}" else none)
    s!"  wire " ++ String.intercalate ", " ws ++ ";")
  let assigns := (List.range len).map (fun k =>
    match P.lines[k]? with
    | some ins => s!"  assign r{k} = {instrStr cfg ins};"
    | none => "")
  let outAssigns := (List.range P.outs.length).map (fun k =>
    match P.outs[k]? with
    | some a => s!"  assign {cfg.outputName k} = {argStr cfg a};"
    | none => "")
  String.intercalate "\n"
    (hdr ++ [s!"module {cfg.moduleName} ("] ++ ports ++ [");"]
      ++ wireDecls ++ [""] ++ assigns ++ [""] ++ outAssigns ++ ["endmodule", ""])

/-- A self-checking testbench over a two-input, one-output DUT: applies each vector,
compares with `!==`, counts failures. Expected values are computed in Lean by
`Prog.run` — the cross-system check. -/
def emitVerilogTB (tbName dutName : String) (aw bw pw : ℕ)
    (vectors : List (String × String × String)) : String :=
  let checks := vectors.map (fun v =>
    s!"    a = {v.1}; b = {v.2.1}; #1;\n" ++
    s!"    if (p !== {v.2.2}) begin errors = errors + 1; " ++
    s!"$display(\"FAIL a=%b b=%b p=%b exp={v.2.2}\", a, b, p); end")
  String.intercalate "\n"
    (["`timescale 1ns/1ns",
      s!"module {tbName};",
      s!"  reg [{aw - 1}:0] a;",
      s!"  reg [{bw - 1}:0] b;",
      s!"  wire [{pw - 1}:0] p;",
      "  integer errors;",
      s!"  {dutName} dut (.a(a), .b(b), .p(p));",
      "  initial begin",
      "    errors = 0;"]
      ++ checks ++
      [s!"    if (errors == 0) $display(\"PASS: {vectors.length} vectors\");",
       "    else $display(\"%0d FAILURES\", errors);",
       "    $finish;",
       "  end",
       "endmodule", ""])

/-! ## The Boolean instantiation and the two flagship configurations -/

/-- The Boolean gate signature's operator tables. -/
def boolCfg (moduleName : String) (portDecls : List String)
    (inputName outputName : ℕ → String) (header : List String) :
    EmitCfg Bool BoolUn BoolBin :=
  { moduleName := moduleName
    portDecls := portDecls
    inputName := inputName
    outputName := outputName
    cstStr := fun b => if b then "1'b1" else "1'b0"
    unOp := fun _ => "~"
    binOp := fun o => match o with
      | .band => "&"
      | .bxor => "^"
    header := header }

/-- Split-operand input naming: wires `0..w-1` are `a`, wires `w..2w-1` are `b` (the
`Fin.append` convention `bilinNet` uses). -/
def abInputs (w : ℕ) (i : ℕ) : String :=
  if i < w then s!"a[{i}]" else s!"b[{i - w}]"

def gf16Cfg : EmitCfg Bool BoolUn BoolBin :=
  boolCfg "gf16_mul"
    ["input  wire [3:0] a", "input  wire [3:0] b", "output wire [3:0] p"]
    (abInputs 4) (fun k => s!"p[{k}]")
    ["gf16_mul - certified GF(2^4) multiplier, nu4 = X^4+X^3+X^2+X+1 (Phi_5).",
     "Emitted from: ECCLib.gf16Prog",
     "  = compileNet (cfoldVec (bilinNet (tbl r4)))   [ECCLib/StraightlineEmit.lean]",
     "37 operator assigns (honest shared count; tree count 105), depth 5.",
     "Semantics certified in Lean: compileNet_run (= evalVec, all inputs),",
     "compileNet_gates_le, compileProg_nodup, compileProg_depth.",
     "This text is UNVERIFIED output of a verified object (the emission trust",
     "boundary); the companion testbench gf16_mul_tb.v carries Lean-computed",
     "expected vectors for all 256 input pairs."]

def gf256Cfg : EmitCfg Bool BoolUn BoolBin :=
  boolCfg "gf256_mul"
    ["input  wire [7:0] a", "input  wire [7:0] b", "output wire [7:0] p"]
    (abInputs 8) (fun k => s!"p[{k}]")
    ["gf256_mul - certified GF(2^8) multiplier, the AES polynomial X^8+X^4+X^3+X+1.",
     "Emitted from: ECCLib.gf256Prog",
     "  = compileNet (cfoldVec (bilinNet tbl8M))   [ECCLib/StraightlineEmit.lean]",
     "gf256Prog_eq_certified: this IS the certified tree's compile (tbl8M_eq, kernel).",
     "202 operator assigns (honest shared count; tree count 727), depth 9.",
     "Semantics certified in Lean: compileNet_run (= evalVec, all inputs),",
     "compileNet_gates_le, compileProg_nodup, compileProg_depth.",
     "This text is UNVERIFIED output of a verified object (the emission trust",
     "boundary); the companion testbench gf256_mul_tb.v carries Lean-computed",
     "expected vectors for ALL 65,536 input pairs."]

/-! ## Testbench vectors, computed by `Prog.run` -/

/-- The `i`-th word of `Fin w → ZMod 2`, bit `k` of `i`. -/
def natWord (w i : ℕ) : Fin w → ZMod 2 := fun k => if i.testBit (k : ℕ) then 1 else 0

/-- A little-endian Bool list as a Verilog binary literal (msb first). -/
def boolsLit (bs : List Bool) : String :=
  s!"{bs.length}'b" ++ String.ofList (bs.reverse.map (fun b => if b then '1' else '0'))

/-- A coordinate word as a Verilog binary literal. -/
def wordLit {w : ℕ} (v : Fin w → ZMod 2) : String := boolsLit (List.ofFn (encW v))

/-- All 256 GF(16) input pairs, with expected outputs from the compiled program. -/
def gf16Vectors : List (String × String × String) :=
  (List.range 256).map (fun t =>
    let va := natWord 4 (t / 16)
    let vb := natWord 4 (t % 16)
    let out := gf16Prog.run boolInterp (Fin.append (encW va) (encW vb))
    (wordLit va, wordLit vb, boolsLit out))

/-- ALL 65,536 GF(256) input pairs — exhaustive, like the GF(16) bench: for a
combinational circuit this makes the external simulation a complete functional
characterization, not a sample. -/
def gf256Vectors : List (String × String × String) :=
  (List.range 65536).map (fun t =>
    let va := natWord 8 (t / 256)
    let vb := natWord 8 (t % 256)
    let out := gf256Prog.run boolInterp (Fin.append (encW va) (encW vb))
    (wordLit va, wordLit vb, boolsLit out))

end ECCLib
