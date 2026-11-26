import Mathlib

/-!
Audit support definitions.  They carry provenance only; mathematical claims
must be declared in `Claims.lean` or imported modules and proved normally.
-/

namespace LeanArticleAudit

def articleSourceSHA256 : String := "328b1aaa0aabb938fb74a0912634fa1e5a1850f14bbe7b5c36e33acdc5af137a"

structure SourceBinding where
  claimId : String
  claimSHA256 : String
  sourceStartLine : Nat
  sourceEndLine : Nat
deriving Repr, DecidableEq

end LeanArticleAudit
