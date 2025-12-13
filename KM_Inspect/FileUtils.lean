/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/

/-!
# KM_Inspect File Utilities

Minimal file utilities for line counting statistics.
All verification logic uses environment introspection, not text parsing.
-/

namespace KM_Inspect

/-! ## Line Counting -/

/-- Count lines in a file (for statistics only) -/
def countLines (path : System.FilePath) : IO Nat := do
  try
    let content ← IO.FS.readFile path
    return (content.splitOn "\n").length
  catch _ =>
    return 0

end KM_Inspect
