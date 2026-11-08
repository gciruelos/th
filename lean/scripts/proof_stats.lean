import Thesis
import Lean.Util.NumObjs
import Lean.Util.ShareCommon
import Lean.Util.Sorry

/-!
Report theorem-body sizes for the imported Thesis modules. This is a measurement tool,
not part of the formalization: referenced declarations are not unfolded.
-/

set_option maxHeartbeats 0

private structure ModuleStats where
  maxProof : Nat := 0
  maxProofName : Lean.Name := .anonymous
  maxStatement : Nat := 0
  maxStatementName : Lean.Name := .anonymous
  theorems : Nat := 0
  sorries : List Lean.Name := []

open Lean in
run_cmd do
  let env ← getEnv
  let mut rows : Std.HashMap Name ModuleStats := {}
  for mod in env.header.moduleNames do
    if mod == `Thesis || mod.toString.startsWith "Thesis." then
      rows := rows.insert mod {}
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let some row := rows[mod]? | continue
    let .thmInfo thm := info | continue
    -- Hash-cons first so allocation/sharing history does not determine the count.
    let size ← (ShareCommon.shareCommon' thm.value).numObjs
    let statementSize ← (ShareCommon.shareCommon' thm.type).numObjs
    let replace := size > row.maxProof ||
      (size == row.maxProof && name.toString < row.maxProofName.toString)
    let replaceStatement := statementSize > row.maxStatement ||
      (statementSize == row.maxStatement && name.toString < row.maxStatementName.toString)
    let hasSorry := thm.value.hasSorry || thm.type.hasSorry
    rows := rows.insert mod {
      maxProof := if replace then size else row.maxProof
      maxProofName := if replace then name else row.maxProofName
      maxStatement := if replaceStatement then statementSize else row.maxStatement
      maxStatementName := if replaceStatement then name else row.maxStatementName
      theorems := row.theorems + 1
      sorries := if hasSorry then name :: row.sorries else row.sorries }
  let data := rows.toList.map fun (mod, row) => Json.mkObj [
    ("module", toJson mod.toString),
    ("max_dag", toJson row.maxProof),
    ("max_declaration", toJson row.maxProofName.toString),
    ("max_statement_dag", toJson row.maxStatement),
    ("max_statement_declaration", toJson row.maxStatementName.toString),
    ("theorems", toJson row.theorems),
    ("sorries", toJson (row.sorries.map Name.toString))]
  IO.println ("THESIS_STATS_JSON\t" ++ (toJson data).compress)
