-- VIOLATION: Missing `module` keyword
-- This makes helperLemma visible to any importer
import Mathlib.Logic.Basic

/-- This helper will be visible externally (leaked) -/
def helperLemma : Nat := 42
