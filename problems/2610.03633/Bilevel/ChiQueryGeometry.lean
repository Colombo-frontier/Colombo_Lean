import Bilevel.PrimitiveQueryGeometry
import Bilevel.ChiCertifiedOracleProperty

/-! Public finite-dimensional geometry for the canonical hierarchy. The
choice of Borel structures contains no hidden frame or objective data. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry ChiCarrier ChiExtension PartialLegendre
set_option autoImplicit false

abbrev CanonicalX (J dim : ℕ) := Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim))
abbrev CanonicalY (J dim : ℕ) := Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals (2*J))
abbrev CanonicalQ (J dim : ℕ) := Joint (CanonicalX J dim) (CanonicalY J dim)

def canonicalGeometry (J dim : ℕ) (hJ : 1≤J) : Geometry := by
  letI : NeZero (2*J) := ⟨by omega⟩
  letI : MeasurableSpace (CanonicalX J dim) := borel _
  letI : BorelSpace (CanonicalX J dim) := ⟨rfl⟩
  letI : MeasurableSpace (CanonicalY J dim) := borel _
  letI : BorelSpace (CanonicalY J dim) := ⟨rfl⟩
  letI : MeasurableSpace (CanonicalQ J dim) := borel _
  letI : BorelSpace (CanonicalQ J dim) := ⟨rfl⟩
  exact Geometry.of (CanonicalX J dim) (CanonicalY J dim)

end Bilevel.PrimitiveQuery
