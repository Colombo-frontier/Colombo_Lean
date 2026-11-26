import NCConcave16991.MixedHaarCanonicalEquiv
import NCConcave16991.MixedHaarCanonicalRankOne
import NCConcave16991.MixedHaarProbabilityTransport

/-! # Actual Haar laws in canonical tail and one-point coordinates -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem tailStabilizerEquiv_preserving {k : ℕ} (r : Fin (k + 1)) :
    MeasurePreserving (tailStabilizerEquiv r) (Haar.haarLaw (k - r.val))
      (Haar.subgroupHaarLaw (prefixStabilizer r) (prefixStabilizer_closed r)) :=
  closedSubgroupHaar_transport _ _ (tailStabilizerEquiv r).toMonoidHom
    (tailStabilizerEquiv_continuous r) (tailStabilizerEquiv r).surjective

theorem prefixStabilizer_rankOne_eq {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) :
    prefixStabilizer r = pointStabilizer (prefixVector r hr) := by
  ext Q
  change (∀ x : prefixSpan r, Haar.orthogonalLinearIsometryEquiv Q (x : EuclideanSpace ℝ (Fin k)) = x) ↔
    ∀ _i : Fin 1, Haar.orthogonalLinearIsometryEquiv Q (prefixVector r hr) = prefixVector r hr
  constructor
  · intro h i
    exact h ⟨prefixVector r hr,prefixVector_mem r hr⟩
  · intro h x
    have hx : (x : EuclideanSpace ℝ (Fin k)) ∈ Submodule.span ℝ ({prefixVector r hr} : Set _) := by
      rw [← prefixSpan_eq_span_prefixVector r hr]
      exact x.property
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx
    rw [← ha,map_smul,h (0 : Fin 1)]

def prefixPointEquiv {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) :
    prefixStabilizer r ≃* pointStabilizer (prefixVector r hr) where
  toFun Q := ⟨Q.val,by rw [← prefixStabilizer_rankOne_eq r hr]; exact Q.property⟩
  invFun Q := ⟨Q.val,by rw [prefixStabilizer_rankOne_eq r hr]; exact Q.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem prefixPointEquiv_continuous {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) :
    Continuous (prefixPointEquiv r hr) := continuous_subtype_val.subtype_mk _

def pointTailEquiv {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) :
    Haar.OrthogonalGroup (k - r.val) ≃* pointStabilizer (prefixVector r hr) :=
  (tailStabilizerEquiv r).trans (prefixPointEquiv r hr)

theorem pointTailEquiv_continuous {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) :
    Continuous (pointTailEquiv r hr) :=
  (prefixPointEquiv_continuous r hr).comp (tailStabilizerEquiv_continuous r)

theorem pointTailEquiv_val {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1)
    (Q : Haar.OrthogonalGroup (k - r.val)) : (pointTailEquiv r hr Q).val = tailOrthogonal r Q := rfl

/-- The ordinary smaller orthogonal Haar draw is exactly the genuine
normalized point-stabilizer Haar law used by the inverse-reveal kernel. -/
theorem pointTailEquiv_preserving {k : ℕ} (r : Fin (k + 1)) (hr : r.val = 1) :
    MeasurePreserving (pointTailEquiv r hr) (Haar.haarLaw (k - r.val))
      (pointStabilizerLaw (prefixVector r hr)) :=
  pointStabilizerHaar_transport _ (pointTailEquiv r hr).toMonoidHom
    (pointTailEquiv_continuous r hr) (pointTailEquiv r hr).surjective

end NCConcave16991.MixedHaar
