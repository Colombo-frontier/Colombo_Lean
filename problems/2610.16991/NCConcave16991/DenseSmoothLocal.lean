import NCConcave16991.DenseSmoothConstruction
import NCConcave16991.ConeSmoothLocalRules
import NCConcave16991.ConeSmoothGeometry
import NCConcave16991.ConeSmoothOverlap

/-! # Actual dimension-free Hessian bounds for one gated radial link -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open ConeSmooth Set
open scoped ContDiff InnerProductSpace Topology

set_option maxHeartbeats 700000
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem jet_add_const {f : F → ℝ} {A B C : ℝ}
    (hf : LocalJetBound univ f A B C) (a : ℝ) :
    LocalJetBound univ (fun x ↦ f x + a) (A + |a|) B C := by
  refine ⟨hf.smooth.add contDiff_const, add_nonneg hf.A_nonneg (abs_nonneg _),
    hf.B_nonneg, hf.C_nonneg, ?_, ?_, ?_⟩
  · intro x hx
    exact (abs_add_le _ _).trans (add_le_add (hf.value x hx) le_rfl)
  · intro x hx
    rw [fderiv_add_const]
    exact hf.first x hx
  · intro x hx y hy
    rw [fderiv_add_const, fderiv_add_const]
    exact hf.second x hx y hy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem radial_jet (u : E) (hu : ‖u‖ = 1) (P : F →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    LocalJetBound univ (fun x ↦ radialCoordinate u (P x)) 1 1 2 := by
  have hh := (radialCoordinate_derivativeBound u hu).comp_contraction P hP
  exact ⟨hh.smooth, by norm_num, hh.first_nonneg, hh.second_nonneg,
    fun x _ ↦ (abs_radialCoordinate_lt_one hu _).le,
    fun x _ ↦ hh.first x, fun x _ y _ ↦ hh.second x y⟩

theorem scaled_radial_jet {ρ : ℝ} (hρ : 0 < ρ) (u : E) (hu : ‖u‖ = 1)
    (P : F →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    LocalJetBound univ (fun x ↦ scaledRadialCoordinate ρ u (P x)) ρ⁻¹ ρ⁻¹ (2 * ρ⁻¹) := by
  have hh := ((radialCoordinate_derivativeBound u hu).comp_contraction P hP).const_mul ρ⁻¹
  simp only [abs_inv, abs_of_pos hρ, mul_one] at hh
  refine ⟨hh.smooth, by positivity, by positivity, by positivity, ?_, fun x _ ↦ hh.first x, ?_⟩
  · intro x _
    rw [scaledRadialCoordinate, abs_mul, abs_inv, abs_of_pos hρ]
    exact (mul_le_mul_of_nonneg_left (abs_radialCoordinate_lt_one hu _).le (inv_pos.mpr hρ).le).trans_eq (mul_one _)
  · intro x _ y _
    exact (hh.second x y).trans_eq (by ring)

theorem gate_radial_jet (u : E) (hu : ‖u‖ = 1) (P : F →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    LocalJetBound univ (fun x ↦ gate (radialCoordinate u (P x))) 1 16 (32 + 64 * densitySlopeBound) := by
  have hh := ((radialCoordinate_derivativeBound u hu).comp_contraction P hP).scalar_comp
    gate gateD gate_contDiff gate_hasDerivAt (by norm_num : (0 : ℝ) ≤ 16)
    (mul_nonneg (by norm_num) densitySlopeBound_nonneg)
    (fun s ↦ by rw [abs_of_nonneg (gateD_nonneg s)]; exact gateD_le s) gateD_sub_bound
  norm_num only [mul_one, one_pow] at hh
  refine ⟨hh.smooth, by norm_num, hh.first_nonneg, hh.second_nonneg,
    fun x _ ↦ ?_, fun x _ ↦ hh.first x, fun x _ y _ ↦ hh.second x y⟩
  rw [abs_of_nonneg (gate_mem_Icc _).1]
  exact (gate_mem_Icc _).2

def localCore (initial : Bool) (ρ : ℝ) (previous row : E) (p : Pair E) : ℝ :=
  if initial then -scaledRadialCoordinate ρ row p.snd else
    -(gate (radialCoordinate previous p.fst) * (scaledRadialCoordinate ρ row p.snd + 1))

theorem localCore_contDiff (initial : Bool) (ρ : ℝ) (previous row : E) :
    ContDiff ℝ ∞ (localCore initial ρ previous row) := by
  cases initial
  · exact ((gate_contDiff.comp ((radialCoordinate_contDiff previous).comp (pairZ (E := E)).contDiff)).mul
      ((contDiff_const.mul ((radialCoordinate_contDiff row).comp (pairU (E := E)).contDiff)).add contDiff_const)).neg
  · exact (contDiff_const.mul ((radialCoordinate_contDiff row).comp (pairU (E := E)).contDiff)).neg

theorem localCore_hessian_bound (initial : Bool) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (previous row : E) (hp : ‖previous‖ = 1) (hr : ‖row‖ = 1) (x : Pair E) :
    ‖fderiv ℝ (fderiv ℝ (localCore initial ρ previous row)) x‖ ≤
      500 * (1 + densitySlopeBound) / ρ := by
  have hs := scaled_radial_jet hρ row hr (pairU (E := E)) pairU_norm
  have hneg (f : Pair E → ℝ) : fderiv ℝ (fderiv ℝ (fun z ↦ -f z)) x =
      -fderiv ℝ (fderiv ℝ f) x := by
    have he : fderiv ℝ (fun z ↦ -f z) = fun z ↦ -fderiv ℝ f z := funext (fun _ ↦ fderiv_fun_neg)
    rw [he, fderiv_fun_neg]
  cases initial
  · have hg := gate_radial_jet previous hp (pairZ (E := E)) pairZ_norm
    have hb := (jet_add_const hs 1).weaken (A' := 2 * ρ⁻¹) (B' := ρ⁻¹) (C' := 2 * ρ⁻¹)
      (by rw [abs_one]; have hh : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).mpr hρ1; linarith) le_rfl le_rfl
    have hh := (hg.mul hb convex_univ).hessian_bound (x := x) (mem_univ x) (Filter.univ_mem)
    change ‖fderiv ℝ (fderiv ℝ (fun p : Pair E ↦
      -(gate (radialCoordinate previous p.fst) * (scaledRadialCoordinate ρ row p.snd + 1)))) x‖ ≤ _
    rw [hneg, norm_neg]
    apply hh.trans
    have hc := densitySlopeBound_nonneg
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hρ]
  · change ‖fderiv ℝ (fderiv ℝ (fun p : Pair E ↦ -scaledRadialCoordinate ρ row p.snd)) x‖ ≤ _
    rw [hneg, norm_neg]
    apply (hs.hessian_bound (mem_univ x) Filter.univ_mem).trans
    have hc := densitySlopeBound_nonneg
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hρ]

end NCConcave16991.DenseSmooth
