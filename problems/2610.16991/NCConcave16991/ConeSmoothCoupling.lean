import NCConcave16991.ConeSmoothClock
import NCConcave16991.ConeSmoothSource

/-! # Actual dimension-free Hessian bound for a gated selected-row source -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives ConeRadial ConeClockGap Set
open scoped ContDiff Topology InnerProductSpace

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def gateFunction (initial : Bool) (q : ℝ) (v : E) (U : H →L[ℝ] E) (x : H) : ℝ :=
  if initial then 1 else exitGate q v (U x)

theorem gateFunction_localJet (S : Set H) (initial : Bool) {q : ℝ} (hq : 0 < q)
    (v : E) (hv : ‖v‖ = 1) (U : H →L[ℝ] E) (hU : ‖U‖ ≤ 1) :
    LocalJetBound S (gateFunction initial q v U) 1 (4 / q)
      (4 * (densitySlopeBound + 1) / q ^ 2) := by
  have hC : 0 ≤ 4 * (densitySlopeBound + 1) / q ^ 2 := by
    have hc := densitySlopeBound_nonneg
    positivity
  cases initial with
  | false =>
      have hb := (exitGate_derivativeBound hq v hv).comp_contraction U hU
      refine ⟨hb.smooth, by norm_num, hb.first_nonneg, hb.second_nonneg, ?_, ?_, ?_⟩
      · intro x hx
        simpa only [gateFunction, Bool.false_eq_true, ite_false,
          abs_of_nonneg (exitGate_bounds q v (U x)).1] using (exitGate_bounds q v (U x)).2
      · intro x hx
        exact hb.first x
      · intro x hx y hy
        exact hb.second x y
  | true =>
      have hconst (z : H) : fderiv ℝ (fun _ : H ↦ (1 : ℝ)) z = 0 :=
        (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).fderiv
      refine ⟨contDiff_const, by norm_num, by positivity, hC, ?_, ?_, ?_⟩
      · intro x hx
        norm_num [gateFunction]
      · intro x hx
        change ‖fderiv ℝ (fun _ : H ↦ (1 : ℝ)) x‖ ≤ 4 / q
        rw [hconst, norm_zero]
        positivity
      · intro x hx y hy
        change ‖fderiv ℝ (fun _ : H ↦ (1 : ℝ)) x - fderiv ℝ (fun _ : H ↦ (1 : ℝ)) y‖ ≤ _
        rw [hconst, hconst, sub_self, norm_zero]
        exact mul_nonneg hC (norm_nonneg _)

def gatedSource (n : ℕ) (initial : Bool) (R q : ℝ) (v w : E)
    (P U Q : H →L[ℝ] E) (x : H) : ℝ :=
  gateFunction initial q v U x * sourceFunction n R w P Q x

theorem gatedSource_localJet (n : ℕ) (initial : Bool) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R)
    (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2) (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (P U Q : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hU : ‖U‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    LocalJetBound (dualCylinder Q R) (gatedSource n initial R q v w P U Q)
      (2 * (3 + Real.sqrt (n : ℝ)))
      (6 * q + (2 * (3 + Real.sqrt (n : ℝ))) * (4 / q)) (92 + 32 * densitySlopeBound) := by
  have hq0 : 0 < q := by linarith
  have hg := gateFunction_localJet (dualCylinder Q R) initial hq0 v hv U hU
  have hs := sourceFunction_localJet n hR hq hrel w hw P Q hP hQ
  have hh := hg.mul hs (dualCylinder_convex Q R)
  have hC : 1 * 12 + (2 * (3 + Real.sqrt (n : ℝ))) * (4 * (densitySlopeBound + 1) / q ^ 2) +
      2 * (4 / q) * (6 * q) ≤ 92 + 32 * densitySlopeBound := by
    have hA : 3 + Real.sqrt (n : ℝ) ≤ 4 * q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
    have hc := densitySlopeBound_nonneg
    have he : 1 * 12 + (2 * (3 + Real.sqrt (n : ℝ))) * (4 * (densitySlopeBound + 1) / q ^ 2) +
        2 * (4 / q) * (6 * q) = 60 + (8 * (3 + Real.sqrt (n : ℝ)) * (densitySlopeBound + 1)) / q ^ 2 := by
      field_simp
      ring
    rw [he]
    have hb : (8 * (3 + Real.sqrt (n : ℝ)) * (densitySlopeBound + 1)) / q ^ 2 ≤
        32 * (densitySlopeBound + 1) := by
      apply (div_le_iff₀ (sq_pos_of_pos hq0)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ 8 * (densitySlopeBound + 1))]
    linarith
  have hb := hh.weaken (le_rfl) (le_rfl) hC
  simp only [one_mul] at hb
  convert hb using 1
  rfl

theorem gatedSource_hessian_bound (n : ℕ) (initial : Bool) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R)
    (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2) (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (P U Q : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hU : ‖U‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (x : H) (hx : ‖Q x‖ ≤ R) :
    ‖fderiv ℝ (fderiv ℝ (gatedSource n initial R q v w P U Q)) x‖ ≤
      92 + 32 * densitySlopeBound := by
  have hb := gatedSource_localJet n initial hR hq hrel hq2 v w hv hw P U Q hP hU hQ
  have hx' : x ∈ dualCylinder Q R := by change ‖Q x‖ ≤ 2 * R; linarith
  apply hb.hessian_bound hx'
  have hn : ∀ᶠ y in 𝓝 x, ‖Q y‖ < 2 * R :=
    (isOpen_lt (continuous_norm.comp Q.continuous) continuous_const).mem_nhds
      (show ‖Q x‖ < 2 * R by linarith)
  exact Filter.mem_of_superset hn (fun y hy ↦ (show ‖Q y‖ ≤ 2 * R from hy.le))

end NCConcave16991.ConeSmooth
