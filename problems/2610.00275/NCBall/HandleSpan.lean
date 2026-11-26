import NCBall.NoisyHandleGeometry

/-! # Arbitrary repeated queries reduce to fresh directions inside each handle -/

noncomputable section
open Submodule
open scoped InnerProductSpace
namespace NCBall

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {H : ℕ}

def handleObservedSpan (L : List (Fin H × F)) (h : Fin H) : Submodule ℝ F :=
  Submodule.span ℝ {a | (h, a) ∈ L}

/-- This holds for any residual projector with the exact nullspace of the
recorded queries, including arbitrary repeated and linearly dependent queries. -/
theorem repeated_handle_innovation_bound (σ : ℝ) (hσ : 0 < σ)
    (L : List (Fin H × F)) (Q : HandleLatent F H →L[ℝ] HandleLatent F H)
    (hQ : IsResidualProjection Q)
    (hfix : ∀ x, Q x = x ↔ ∀ q ∈ L, ⟪noisyHandleDirection F σ q.1 q.2, x⟫_ℝ = 0)
    (h : Fin H) (a : F) :
    ‖hiddenBlock F H (normalizedInnovation Q (noisyHandleDirection F σ h a))‖ ^ 2 ≤
      1 / σ ^ 2 := by
  classical
  let K := handleObservedSpan L h
  let k : F := K.orthogonalProjection a
  let b : F := a - k
  have hkill (q : Fin H × F) (hq : q ∈ L) : Q (noisyHandleDirection F σ q.1 q.2) = 0 := by
    let r := noisyHandleDirection F σ q.1 q.2
    have hr := (hfix (Q r)).mp (hQ.1 r) q hq
    have he := hQ.2 r (Q r)
    rw [hQ.1, hr] at he
    exact inner_self_eq_zero.mp he
  have hK : K ≤ LinearMap.ker (Q.comp (noisyHandleDirection F σ h)).toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    exact hkill (h, x) hx
  have hkillk : Q (noisyHandleDirection F σ h k) = 0 :=
    hK (K.orthogonalProjection a).property
  have hres : Q (noisyHandleDirection F σ h a) = Q (noisyHandleDirection F σ h b) := by
    dsimp [b]
    rw [map_sub, map_sub, hkillk, sub_zero]
  by_cases hb : b = 0
  · simp [normalizedInnovation, hres, hb]
    positivity
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let r := ‖b‖⁻¹ • b
  have hr : ‖r‖ = 1 := by
    simp [r, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbn), hbn.ne']
  have hbr : b = ‖b‖ • r := by simp [r, smul_smul, hbn.ne']
  have horth (x : F) (hx : (h, x) ∈ L) : ⟪x, r⟫_ℝ = 0 := by
    have hxK : x ∈ K := Submodule.subset_span hx
    have he := K.orthogonalProjection_inner_eq_zero a x hxK
    change ⟪b, x⟫_ℝ = 0 at he
    rw [real_inner_comm] at he
    simp [r, inner_smul_right, he]
  have hfresh : Q (handleBlock F h.succ r) = handleBlock F h.succ r := by
    apply (hfix _).mpr
    rintro ⟨j, x⟩ hx
    rw [noisyHandleDirection_inner_noise]
    by_cases hj : j = h
    · subst j
      simp [horth x hx]
    · simp [hj]
  have he : Q (noisyHandleDirection F σ h a) =
      ‖b‖ • Q (noisyHandleDirection F σ h r) := by
    conv_lhs => rw [hres, hbr, map_smul, map_smul]
  rw [normalizedInnovation_eq_of_rescale Q _ _ hbn he]
  exact handle_fresh_innovation_bound σ hσ Q hQ h r hr hfresh

end NCBall
