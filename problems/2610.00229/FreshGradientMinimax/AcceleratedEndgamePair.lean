import FreshGradientMinimax.AcceleratedIdealGradient
import FreshGradientMinimax.AcceleratedScalarEndgame

/-! Selecting the first small z coordinate supplies a concrete pair of
actual ideal derivatives for the robust endgame. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem interleavedX_eq_zero {k : ℕ} (i : Fin k) (hi : i.val = 0) : interleavedX i = 0 := by
  apply Fin.ext
  simp [interleavedX, finProdFinEquiv, hi]

theorem interleavedX_eq_previous {k : ℕ} (i : Fin k) (hi : 0 < i.val) :
    interleavedX i = interleavedNextX (⟨i.val - 1, by omega⟩ : Fin k) := by
  apply Fin.ext
  change 0 + 2 * i.val = (1 + 2 * (i.val - 1)) + 1
  omega

theorem acceleratedNonlinearGradient_x_sign {k : ℕ} (q : Euclid (k * 2 + 1)) (i : Fin k) :
    -6 ≤ acceleratedNonlinearGradient q (interleavedX i) ∧ acceleratedNonlinearGradient q (interleavedX i) ≤ 0 := by
  by_cases hi : i.val = 0
  · rw [interleavedX_eq_zero i hi, acceleratedNonlinearGradient_zero]
    constructor <;> linarith only [coreDensity_pos (q 0), coreDensity_le_one (q 0)]
  · rw [interleavedX_eq_previous i (by omega), acceleratedNonlinearGradient_nextX]
    exact ⟨(abs_le.mp (coreLinkTermD2_bound _ _)).1, coreLinkTermD2_nonpos _ _⟩

theorem acceleratedNonlinearGradient_x_barrier {k : ℕ} (u : Euclid (k * 2 + 1)) (i : Fin k)
    (hprev : ∀ j : Fin k, j.val < i.val → 1 ≤ |u (interleavedZ j)|)
    (hv : |u (interleavedX i)| < 1) :
    acceleratedNonlinearGradient (clipVector 2 u) (interleavedX i) ≤ -primalBarrierConstant := by
  have hclip : smoothClip 2 (u (interleavedX i)) = u (interleavedX i) :=
    smoothClip_identity (by norm_num) (by linarith only [hv])
  by_cases hi : i.val = 0
  · rw [interleavedX_eq_zero i hi, acceleratedNonlinearGradient_zero, clipVector_apply]
    rw [interleavedX_eq_zero i hi] at hclip hv
    rw [hclip]
    exact neg_le_neg (coreDensity_lower_on_unit hv.le)
  · let j : Fin k := ⟨i.val - 1, by omega⟩
    have hij : interleavedX i = interleavedNextX j := interleavedX_eq_previous i (by omega)
    rw [hij, acceleratedNonlinearGradient_nextX, clipVector_apply, clipVector_apply, ← hij, hclip]
    exact coreLinkTermD2_barrier (smoothClip_two_abs_ge_one (hprev j (by dsimp only [j]; omega))) hv.le

theorem accelerated_first_small_z {k : ℕ} (u : Euclid (k * 2 + 1))
    (hex : ∃ i : Fin k, |u (interleavedZ i)| < 1) :
    ∃ i : Fin k, |u (interleavedZ i)| < 1 ∧ ∀ j : Fin k, j.val < i.val → 1 ≤ |u (interleavedZ j)| := by
  classical
  let P : ℕ → Prop := fun j => ∃ hj : j < k, |u (interleavedZ (⟨j, hj⟩ : Fin k))| < 1
  have hP : ∃ j, P j := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i.val, i.isLt, hi⟩
  obtain ⟨hi, hs⟩ := Nat.find_spec hP
  refine ⟨⟨Nat.find hP, hi⟩, hs, ?_⟩
  intro j hj
  by_contra h
  have hjP : P j.val := ⟨j.isLt, lt_of_not_ge h⟩
  exact (not_le_of_gt hj) (Nat.find_min' hP hjP)

theorem acceleratedIdealGradient_z_small {k : ℕ} (u : Euclid (k * 2 + 1)) (i : Fin k)
    (hz : |u (interleavedZ i)| < 1) :
    acceleratedIdealGradient u (interleavedZ i) =
      coreLinkTermD1 (u (interleavedZ i)) (smoothClip 2 (u (interleavedNextX i))) -
        6 * (smoothClip 2 (u (interleavedX i)) - u (interleavedZ i) / 2) := by
  rw [acceleratedIdealGradient_z, smoothClipSlope_identity (by norm_num) (by linarith only [hz]),
    smoothClip_identity (by norm_num) (by linarith only [hz]), one_mul]

end FreshGradientMinimax
