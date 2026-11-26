import NCConcave16991.MixedHaarCanonicalTail
import NCConcave16991.MixedHaarHouseholder
import NCConcave16991.PartialIsometryCompletion
import NCConcave16991.ConditionalHaarCompletion

/-! # Canonical tail orthogonal matrices and their prefix stabilizer -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set MeasureTheory

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem orthogonal_eq_of_action_eq {k : ℕ} (Q R : Haar.OrthogonalGroup k)
    (h : ∀ x : EuclideanSpace ℝ (Fin k), Haar.orthogonalLinearIsometryEquiv Q x = Haar.orthogonalLinearIsometryEquiv R x) : Q = R := by
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun x : EuclideanSpace ℝ (Fin k) ↦ x i) (h ((EuclideanSpace.basisFun (Fin k) ℝ) j))
  change (Q.val.mulVec (WithLp.ofLp ((EuclideanSpace.basisFun (Fin k) ℝ) j))) i =
    (R.val.mulVec (WithLp.ofLp ((EuclideanSpace.basisFun (Fin k) ℝ) j))) i at hh
  simpa only [EuclideanSpace.basisFun_apply,EuclideanSpace.single,PiLp.ofLp_single,
    Matrix.mulVec_single_one,Matrix.col_apply] using hh

def prefixStabilizer {k : ℕ} (r : Fin (k + 1)) : Subgroup (Haar.OrthogonalGroup k) :=
  Haar.inputStabilizer (fun x : prefixSpan r ↦ (x : EuclideanSpace ℝ (Fin k)))

theorem prefixStabilizer_closed {k : ℕ} (r : Fin (k + 1)) :
    IsClosed (prefixStabilizer r : Set (Haar.OrthogonalGroup k)) := by
  change IsClosed {Q : Haar.OrthogonalGroup k | ∀ x : prefixSpan r,
    Haar.orthogonalLinearIsometryEquiv Q (x : EuclideanSpace ℝ (Fin k)) = x}
  simp_rw [setOf_forall]
  exact isClosed_iInter (fun x ↦ isClosed_eq (Haar.continuous_orthogonalLinearIsometryEquiv_apply x.val)
    continuous_const)

def complementAction {k : ℕ} (r : Fin (k + 1)) (V : Haar.OrthogonalGroup (k - r.val)) :
    (prefixSpan r)ᗮ ≃ₗᵢ[ℝ] (prefixSpan r)ᗮ :=
  ((tailIsometry r).symm.trans (Haar.orthogonalLinearIsometryEquiv V)).trans (tailIsometry r)

def tailCompletionIsometry {k : ℕ} (r : Fin (k + 1)) (V : Haar.OrthogonalGroup (k - r.val)) :
    EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
  PartialIsometry.completion (prefixSpan r) (prefixSpan r) (.refl ℝ _) (complementAction r V)

def tailOrthogonal {k : ℕ} (r : Fin (k + 1)) (V : Haar.OrthogonalGroup (k - r.val)) : Haar.OrthogonalGroup k :=
  orthogonalOfIsometry (tailCompletionIsometry r V)

theorem tailOrthogonal_fixes_prefix {k : ℕ} (r : Fin (k + 1))
    (V : Haar.OrthogonalGroup (k - r.val)) (x : prefixSpan r) :
    Haar.orthogonalLinearIsometryEquiv (tailOrthogonal r V) (x : EuclideanSpace ℝ (Fin k)) = x := by
  rw [tailOrthogonal,orthogonalOfIsometry_action]
  exact PartialIsometry.completion_on_domain (prefixSpan r) (prefixSpan r) (.refl ℝ _) _ x

theorem tailOrthogonal_mem_stabilizer {k : ℕ} (r : Fin (k + 1))
    (V : Haar.OrthogonalGroup (k - r.val)) : tailOrthogonal r V ∈ prefixStabilizer r :=
  tailOrthogonal_fixes_prefix r V

theorem tailOrthogonal_on_tail {k : ℕ} (r : Fin (k + 1))
    (V : Haar.OrthogonalGroup (k - r.val)) (v : EuclideanSpace ℝ (Fin (k - r.val))) :
    Haar.orthogonalLinearIsometryEquiv (tailOrthogonal r V) (tailIsometry r v : EuclideanSpace ℝ (Fin k)) =
      (tailIsometry r (Haar.orthogonalLinearIsometryEquiv V v) : EuclideanSpace ℝ (Fin k)) := by
  rw [tailOrthogonal,orthogonalOfIsometry_action]
  simp only [tailCompletionIsometry,PartialIsometry.completion_on_complement,complementAction,
    LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply]

theorem tailOrthogonal_apply {k : ℕ} (r : Fin (k + 1))
    (V : Haar.OrthogonalGroup (k - r.val)) (x : EuclideanSpace ℝ (Fin k)) :
    Haar.orthogonalLinearIsometryEquiv (tailOrthogonal r V) x =
      ((prefixSpan r).orthogonalProjectionOnto x : EuclideanSpace ℝ (Fin k)) +
        (tailIsometry r (Haar.orthogonalLinearIsometryEquiv V
          ((tailIsometry r).symm ((prefixSpan r)ᗮ.orthogonalProjectionOnto x))) : EuclideanSpace ℝ (Fin k)) := by
  rw [tailOrthogonal,orthogonalOfIsometry_action]
  simp only [tailCompletionIsometry,PartialIsometry.completion_apply,
    complementAction,LinearIsometryEquiv.trans_apply]
  rfl

theorem tailOrthogonal_entry {k : ℕ} (r : Fin (k + 1))
    (V : Haar.OrthogonalGroup (k - r.val)) (i j : Fin k) :
    (tailOrthogonal r V).val i j =
      let x := (EuclideanSpace.basisFun (Fin k) ℝ) j
      let v := (tailIsometry r).symm ((prefixSpan r)ᗮ.orthogonalProjectionOnto x)
      ((prefixSpan r).orthogonalProjectionOnto x : EuclideanSpace ℝ (Fin k)) i +
        (tailIsometry r (Haar.orthogonalLinearIsometryEquiv V v)).val i := by
  change (orthogonalOfIsometry (tailCompletionIsometry r V)).val i j = _
  rw [orthogonalOfIsometry_entry]
  have hh := tailOrthogonal_apply r V ((EuclideanSpace.basisFun (Fin k) ℝ) j)
  rw [tailOrthogonal,orthogonalOfIsometry_action] at hh
  exact congrArg (fun x : EuclideanSpace ℝ (Fin k) ↦ x i) hh

theorem tailOrthogonal_continuous {k : ℕ} (r : Fin (k + 1)) : Continuous (tailOrthogonal r) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun V ↦ (tailOrthogonal r V).val i j)
  simp_rw [tailOrthogonal_entry]
  have hc := (tailIsometry r).continuous.comp (Haar.continuous_orthogonalLinearIsometryEquiv_apply
    ((tailIsometry r).symm ((prefixSpan r)ᗮ.orthogonalProjectionOnto ((EuclideanSpace.basisFun (Fin k) ℝ) j))))
  exact continuous_const.add ((PiLp.continuous_apply 2 (fun _ : Fin k ↦ ℝ) i).comp
    (continuous_subtype_val.comp hc))

theorem tailOrthogonal_measurable {k : ℕ} (r : Fin (k + 1)) : Measurable (tailOrthogonal r) :=
  (tailOrthogonal_continuous r).measurable

theorem tailOrthogonal_one {k : ℕ} (r : Fin (k + 1)) : tailOrthogonal r 1 = 1 := by
  apply orthogonal_eq_of_action_eq
  intro x
  rw [tailOrthogonal_apply,Haar.action_one,Haar.action_one,LinearIsometryEquiv.apply_symm_apply]
  simpa using (prefixSpan r).orthogonalDecomposition.symm_apply_apply x

theorem tailOrthogonal_mul {k : ℕ} (r : Fin (k + 1))
    (U V : Haar.OrthogonalGroup (k - r.val)) : tailOrthogonal r (U * V) = tailOrthogonal r U * tailOrthogonal r V := by
  apply orthogonal_eq_of_action_eq
  intro x
  rw [Haar.action_mul,tailOrthogonal_apply r V,map_add,tailOrthogonal_fixes_prefix,tailOrthogonal_on_tail,
    tailOrthogonal_apply,Haar.action_mul]

def tailOrthogonalHom {k : ℕ} (r : Fin (k + 1)) : Haar.OrthogonalGroup (k - r.val) →* Haar.OrthogonalGroup k where
  toFun := tailOrthogonal r
  map_one' := tailOrthogonal_one r
  map_mul' := tailOrthogonal_mul r

end NCConcave16991.MixedHaar
