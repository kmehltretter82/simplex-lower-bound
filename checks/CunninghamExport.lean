import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

/- Audit data taken directly from the executable Lean definitions. These
evaluations are comparison evidence, not theorem certificates. -/
namespace CunninghamExport
open FriedmannCunningham

def kindText : Kind → String
  | .a => "a" | .b => "b" | .c => "c" | .d => "d" | .e => "e"

def nameText (v : Name) : String :=
  s!"{kindText v.kind},{v.level},{if v.one then 1 else 0}"

def exportFamily (n : ℕ) : IO Unit := do
  IO.println s!"N|{n}|{rows n}|{cols n}"
  for r in List.finRange (rows n) do
    let v := rowName n r
    IO.println s!"R|{n}|{r.val}|{kindText v.1},{v.2}|{if initialBit v then 1 else 0}"
  for j in List.finRange (cols n) do
    let a := columnName n j
    let entries := (List.finRange (rows n)).map (fun r => toString ((program n).A r j))
    IO.println s!"C|{n}|{j.val}|{nameText a}|{(program n).c j}|{String.intercalate "," entries}|{(actionSource n j).val}|{(actionTarget n a).val}|{columnRank n a}"
  for v in List.finRange (vertices n) do
    let succ := ((List.finRange (vertices n)).filter
      (fun w => decide (w ∈ gameSuccessors n v))).map (fun w => toString w.val)
    IO.println s!"G|{n}|{v.val}|{gamePriority n v}|{String.intercalate "," succ}"

#eval ([3, 4, 5, 6, 7, 8, 9, 10] : List ℕ).forM exportFamily
end CunninghamExport
