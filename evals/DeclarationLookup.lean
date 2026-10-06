import Lean

/- Owner lookup over admitted imports. Input is one bounded JSON object on stdin. The owner supplies
LEAN_PATH, process isolation, deadline and output bounds. Name components never become Lean source.
Theorem proof terms are never emitted. Display text is advisory, not an expression serialization. -/

open Lean

namespace DeclarationLookup

def fail (reason : String) : IO α := throw <| IO.userError reason

def readName (value : Json) (moduleName := false) : IO Name := do
  let parts ← match value.getArr? with
    | .ok parts => pure parts
    | .error reason => fail reason
  if parts.isEmpty || parts.size > 32 then fail "name component count bound"
  let mut name := Name.anonymous
  for value in parts do
    let part ← match value.getStr? with
      | .ok part => pure part
      | .error reason => fail reason
    if part.isEmpty || part.toUTF8.size > 256 || part.contains '\x00' then
      fail "name component byte bound"
    if moduleName && (part.contains '/' || part.contains '\\' || part.contains '.' || part.contains ':') then
      fail "module component contains a path separator"
    name := Name.str name part
  return name

def nameParts (name : Name) : Except String (Array String) := do
  let mut current := name
  let mut parts := #[]
  for _ in [:32] do
    match current with
    | .anonymous => return parts.reverse
    | .str parent part =>
      if part.toUTF8.size > 256 then throw "observed name component byte bound"
      parts := parts.push part
      current := parent
    | .num .. => throw "numeric name components are outside the string-component protocol"
  throw "observed name component count bound"

def partsJson (name : Name) : IO Json := do
  match nameParts name with
  | .ok parts => return toJson parts
  | .error reason => fail reason

def field (request : Json) (name : String) : IO Json := do
  match request.getObjVal? name with
  | .ok value => return value
  | .error reason => fail reason

def bounded (text : String) (limit : Nat) : Json := Id.run do
  let bytes := text.toUTF8
  let mut clipped := text
  if bytes.size > limit then
    clipped := ""
    for delta in [:4] do
      if let some valid := String.fromUTF8? (bytes.extract 0 (limit - delta)) then
        clipped := valid
        break
  return Json.mkObj [("text", toJson clipped), ("bytes", toJson bytes.size),
    ("retained_bytes", toJson clipped.toUTF8.size), ("truncated", toJson (decide (bytes.size > limit)))]

def lookup (environment : Environment) (name : Name) : IO Json := do
  let some info := environment.find? name | return Json.mkObj [("status", toJson "missing"),
    ("name", ← partsJson name), ("display_name", toJson name.toString)]
  let type ← PrettyPrinter.ppExprLegacy environment {} {} {} info.type
  let doc ← findDocString? environment name
  let origin ← match environment.getModuleIdxFor? name with
    | some index =>
      if index.toNat >= environment.header.moduleNames.size then fail "declaration origin index bound"
      partsJson environment.header.moduleNames[index.toNat]!
    | none => fail "imported declaration has no originating module"
  let (kind, body) ← match info with
    | .defnInfo definition =>
      let body ← PrettyPrinter.ppExprLegacy environment {} {} {} definition.value
      pure ("definition", bounded body.pretty 4096)
    | .thmInfo .. => pure ("theorem", Json.null)
    | .axiomInfo .. => pure ("axiom", Json.null)
    | .opaqueInfo .. => pure ("opaque", Json.null)
    | .ctorInfo .. => pure ("constructor", Json.null)
    | .recInfo .. => pure ("recursor", Json.null)
    | .inductInfo .. => pure ("inductive", Json.null)
    | .quotInfo .. => pure ("quotient", Json.null)
  return Json.mkObj [("status", toJson "ok"), ("name", ← partsJson name),
    ("display_name", toJson name.toString), ("kind", toJson kind), ("origin_module", origin),
    ("type", bounded type.pretty 4096), ("docstring", doc.map (bounded · 2048) |>.getD Json.null),
    ("body", body), ("advisory", toJson true)]

def inventory (environment : Environment) : IO Json := do
  if environment.header.moduleNames.size > 10000 then fail "imported module count bound"
  let modules ← environment.header.moduleNames.mapM partsJson
  let result := Json.mkObj [("status", toJson "ok"), ("modules", Json.arr modules),
    ("count", toJson modules.size), ("hashes", Json.null)]
  if result.compress.toUTF8.size > 2 * 1024 * 1024 then fail "inventory output byte bound"
  return result

-- Imported doc/pretty-printer extensions require executing initializers from the owner's admitted
-- compiled modules. This unsafe loader is trusted observation code, never a proof certificate.
unsafe def run (request : Json) : IO Json := do
  let operation ← match (← field request "op").getStr? with
    | .ok operation => pure operation
    | .error reason => fail reason
  if operation != "lookup" && operation != "inventory" then fail "unknown operation"
  let modules ← match (← field request "modules").getArr? with
    | .ok modules => pure modules
    | .error reason => fail reason
  if modules.isEmpty || modules.size > 64 then fail "requested module count bound"
  let names ← modules.mapM (readName · true)
  enableInitializersExecution
  let environment ← importModules (names.map fun name => { module := name }) {} (loadExts := true)
  if operation == "inventory" then inventory environment
  else lookup environment (← readName (← field request "name"))

end DeclarationLookup

unsafe def main : IO UInt32 := do
  searchPathRef.set (← addSearchPathFromEnv [])
  let output ← IO.getStdout
  let result ← try
    let input ← IO.getStdin
    let mut bytes := ByteArray.empty
    for _ in [:16 * 1024 + 1] do
      let chunk ← input.read (16 * 1024 + 1 - bytes.size).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
      if bytes.size > 16 * 1024 then DeclarationLookup.fail "request byte bound"
    let some text := String.fromUTF8? bytes | DeclarationLookup.fail "request is not UTF-8"
    let request ← match Json.parse text with
      | .ok request => pure request
      | .error reason => DeclarationLookup.fail reason
    DeclarationLookup.run request
  catch error => pure <| Json.mkObj [("status", toJson "error"),
    ("reason", DeclarationLookup.bounded error.toString 1024)]
  output.putStrLn result.compress
  return 0
