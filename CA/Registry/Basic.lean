import Batteries.Lean.NameMapAttribute

open Lean

namespace CA.Registry

/-- Metadata for an `@[open_point]` declaration. -/
structure OpenPointEntry where
  description : String := ""
  deriving Inhabited, Repr

/-- Metadata for a `@[publish]` declaration. -/
structure PublishEntry where
  description : String := ""
  deriving Inhabited, Repr

initialize openPointExt : NameMapExtension OpenPointEntry ←
  registerNameMapExtension OpenPointEntry

initialize publishExt : NameMapExtension PublishEntry ←
  registerNameMapExtension PublishEntry

/-- Check if a name is marked `@[open_point]`. -/
def isOpenPoint (env : Environment) (name : Name) : Bool :=
  openPointExt.find? env name |>.isSome

/-- Check if a name is marked `@[publish]`. -/
def isPublished (env : Environment) (name : Name) : Bool :=
  publishExt.find? env name |>.isSome

/-- Get all open point entries from the environment. -/
def getOpenPoints (env : Environment) : List (Name × OpenPointEntry) :=
  (openPointExt.getState env).get.toList

/-- Get all published entries from the environment. -/
def getPublished (env : Environment) : List (Name × PublishEntry) :=
  (publishExt.getState env).get.toList

end CA.Registry
