import Mathlib

/-!
Audit support definitions.  They carry provenance only; mathematical claims
must be declared in `Claims.lean` or imported modules and proved normally.
-/

namespace LeanArticleAudit

def articleSourceSHA256 : String := "d12436b448a12ef6652bc524ef8ce4458cb636e409f5e7982061c1af62e6f178"

structure SourceBinding where
  claimId : String
  claimSHA256 : String
  sourceStartLine : Nat
  sourceEndLine : Nat
deriving Repr, DecidableEq

end LeanArticleAudit
