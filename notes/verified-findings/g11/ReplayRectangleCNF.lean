import RectangleCNFBridge
import Lean.Data.Json

open Std.Sat Std.Tactic.BVDecide RectangleCNFBridge
open FormulaRectPartition

structure Metadata where
  atoms : Array (List Nat)
  rules : Array Nat
  deriving Lean.FromJson

def unpackKey (n : Nat) : KType :=
  (Fin.ofNat 11 (n/65536), Finset.univ.filter fun i : Fin 16 => n.testBit i.val)

def unpackAtom : List Nat → Atom
  | [1,k] => .used (unpackKey k)
  | [2,k,q] => .member (unpackKey k) (Fin.ofNat 24 q)
  | 3 :: t :: ks => .counter ((ks.map unpackKey).toFinset) t
  | _ => .unused

def unpackRule : Nat → Rule
  | 0 => .link
  | 1 => .occupied
  | 2 => .apart
  | 3 => .carry
  | 4 => .bound
  | i+5 => .cell (Fin.ofNat 16 (i/24)) (Fin.ofNat 24 (i%24))

def readFormula (path : System.FilePath) : IO (CNF Nat) := do
  let contents ← IO.FS.readFile path
  let lines := ((contents.splitOn "\n").map String.trimAscii).filter (fun s => !s.isEmpty)
  let header :: clauses := lines | throw (IO.userError "missing DIMACS header")
  let ["p", "cnf", n, k] := header.toString.splitOn " "
    | throw (IO.userError "invalid DIMACS header")
  let some bound := n.toNat? | throw (IO.userError "invalid variable count")
  let some count := k.toNat? | throw (IO.userError "invalid clause count")
  unless clauses.length == count do throw (IO.userError "clause count mismatch")
  let mut result : CNF Nat := ⟨#[]⟩
  for row in clauses do
    let words := row.toString.splitOn " "
    unless words.getLast? == some "0" do throw (IO.userError "unterminated clause")
    let mut clause : CNF.Clause Nat := .empty
    for word in words.dropLast do
      let some lit := word.toInt? | throw (IO.userError "invalid literal")
      unless lit != 0 && lit.natAbs <= bound do throw (IO.userError "out-of-range literal")
      clause := clause.add (lit.natAbs - 1) (lit > 0)
    result := result.add clause
  return result

def main (args : List String) : IO Unit := do
  let [cnfFile, proofFile, metadataFile] := args | throw (IO.userError "expected CNF, LRAT, annotations")
  let cnf ← readFormula cnfFile
  let proof ← LRAT.loadLRATProof proofFile
  let raw ← IO.FS.readFile metadataFile
  let json ← IO.ofExcept (Lean.Json.parse raw)
  let m : Metadata ← IO.ofExcept (Lean.fromJson? json)
  unless m.rules.size = cnf.clauses.size do throw (IO.userError "incorrect annotation count")
  let atoms := m.atoms.map unpackAtom
  let rules := m.rules.map unpackRule
  let d := fun i : Nat => atoms[i]?.getD .unused
  let r := fun i : Nat => rules[i]?.getD .link
  unless validates 22 d r cnf do
    for h : i in [0:cnf.clauses.size] do
      let row := cnf.clauses[i]
      unless check 22 (r i) (annotated d row) do
        throw (IO.userError s!"invalid semantic annotation on physical clause {i+1}, rule {repr (r i)}")
    throw (IO.userError "semantic validation failed")
  unless LRAT.check proof cnf do throw (IO.userError "LRAT rejected")
  IO.println s!"Both premises of certified_lower passed on one CNF: {cnf.clauses.size} physical clauses, {atoms.size} variable meanings, {proof.size} LRAT actions."
