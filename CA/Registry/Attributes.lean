import CA.Registry.Basic
import CA.Util

open Lean
open CA.Util (constantKind)

namespace CA.Registry

private def isDefnInfo : ConstantInfo → Bool
  | .defnInfo _ => true
  | _ => false

/-- Syntax of `@[open_point]` / `@[open_point "description"]`. Without a
    declared `attr` syntax the parser only accepts the bare identifier
    form (`Attr.simple`), so the string argument would be a parse error. -/
syntax (name := open_point) "open_point" (ppSpace str)? : attr

/-- Syntax of `@[publish]` / `@[publish "description"]`. -/
syntax (name := publish) "publish" (ppSpace str)? : attr

/-- The optional string description of an `@[open_point]`/`@[publish]`
    attribute application (`stx[0]` is the keyword atom, `stx[1]` the
    optional string literal). -/
private def parseDescription (stx : Syntax) : String :=
  match stx[1].getOptional? with
  | some lit => (Syntax.isStrLit? lit).getD ""
  | none => ""

/-- `@[open_point]` or `@[open_point "description"]` — marks a `def X : Prop`
    as an open problem in the formal registry. -/
initialize registerBuiltinAttribute {
  name := `open_point
  descr := "Marks a Prop definition as an open problem"
  applicationTime := .afterCompilation
  add := fun name stx _kind => do
    let env ← getEnv
    let some ci := env.find? name
      | throwError "@[open_point]: unknown declaration '{name}'"
    unless isDefnInfo ci do
      throwError "@[open_point]: '{name}' must be a definition, got {constantKind ci}"
    let ty := ci.type
    unless ty == .sort .zero do
      throwError "@[open_point]: '{name}' must have type Prop, got {ty}"
    openPointExt.add name { description := parseDescription stx }
}

/-- `@[publish]` or `@[publish "description"]` — marks a theorem or definition
    for publication to the formal registry. -/
initialize registerBuiltinAttribute {
  name := `publish
  descr := "Marks a declaration for publication to the formal registry"
  applicationTime := .afterCompilation
  add := fun name stx _kind => do
    let env ← getEnv
    let some _ := env.find? name
      | throwError "@[publish]: unknown declaration '{name}'"
    publishExt.add name { description := parseDescription stx }
}

end CA.Registry
