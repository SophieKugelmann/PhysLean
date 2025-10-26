/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Basic
import ImportGraph.Imports
import Mathlib.Lean.CoreM

/-!

# Extracting commands with no doc strings.

-/

open Lean System Meta PhysLean


def Imports.RedundantImports (imp : Import) : MetaM UInt32 := do
  let x ← redundantImports (some imp.module)
  if x.isEmpty then return 0
  println! "\n"
  println! s!"\x1b[31mError: Transitive imports in {Name.toFilePath imp.module} (please remove them):\x1b[0m"
  println! x.toList
  return 0

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports ← allImports
  let _ ← CoreM.withImportModules #[`PhysLean] (imports.mapM Imports.RedundantImports).run'
  return 0
