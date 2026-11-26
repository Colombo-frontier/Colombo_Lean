import Smoothness2601.SineScaling

/-! Uniform signal, derivative-envelope, and actual-objective estimates after
the manuscript's amplitude and spatial rescaling. -/
noncomputable section
namespace Smoothness2601.SineGeometry.Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (F : Profiles X)

theorem source_signal_bound {m c τ s h K : ℝ}
    (hm : 0 ≤ m) (hc : 0 < c) (hτ : 0 < τ) (hs : 0 < s) (_hh : 0 < h)
    (hK : 0 < K) (hl : K*s ≤ h) :
    m*(s^2/(τ*c))*h*(F.sourceScaled hτ hs).C₁+
      m*(s^2/(τ*c))*(F.sourceScaled hτ hs).C₀ ≤
        ((m/c)*(F.C₁+F.C₀/(τ*K)))*s*h := by
  rw [(F.sourceScaled_constants hτ hs).2.2.1,(F.sourceScaled_constants hτ hs).2.1]
  have hb : s^2/τ ≤ s*h/(τ*K) := by
    apply (div_le_div_iff₀ hτ (by positivity : 0 < τ*K)).mpr
    have ht := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ s*τ)
    nlinarith only [ht]
  have hc' := mul_le_mul_of_nonneg_left hb (mul_nonneg (div_nonneg hm hc.le) F.C₀_nonneg)
  calc
    _ = (m/c)*s*h*F.C₁+((m/c)*F.C₀)*(s^2/τ) := by field_simp; ring
    _ ≤ (m/c)*s*h*F.C₁+((m/c)*F.C₀)*(s*h/(τ*K)) := add_le_add_left hc' _
    _ = _ := by ring

theorem source_derivative_coefficient {m c τ s h : ℝ}
    (hm : 0 ≤ m) (hc : 0 < c) (hτ : 0 < τ) (hs : 0 < s) (hh : 0 < h)
    (hrelative : s/(τ*h) ≤ 1) :
    m*(s^2/(τ*c))*((F.sourceScaled hτ hs).C₁+(F.sourceScaled hτ hs).C₀/h) ≤
      ((m/c)*(F.C₁+F.C₀))*s := by
  rw [(F.sourceScaled_constants hτ hs).2.2.1,(F.sourceScaled_constants hτ hs).2.1]
  have hb := mul_le_mul_of_nonneg_left hrelative
    (mul_nonneg (mul_nonneg (div_nonneg hm hc.le) hs.le) F.C₀_nonneg)
  calc
    _ = (m/c)*s*F.C₁+((m/c)*s*F.C₀)*(s/(τ*h)) := by field_simp; ring
    _ ≤ (m/c)*s*F.C₁+((m/c)*s*F.C₀)*1 := add_le_add_left hb _
    _ = _ := by ring

theorem source_uniform_envelope {p : WithTop ℕ} {m c τ s K M Λ β : ℝ}
    (hp : 1 ≤ p) (hm : 0 ≤ m) (hc : 0 < c) (hτ : 0 < τ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hK : 0 < K) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (ht : Real.exp 1^β/(K*Λ) ≤ 1)
    (hscale : ((m/c)*(F.C₁+F.C₀))*(Real.exp 1^β/(K*Λ)) ≤ M*Λ)
    (hsmall : s ≤ τ^2*K^2/((2:ℝ)^β)^2)
    {k : ℕ} (hk : 2 ≤ k) (hkp : (k:WithTop ℕ) ≤ p) :
    m*(s^2/(τ*c))*((F.sourceScaled hτ hs).C₁+
      (F.sourceScaled hτ hs).C₀/sineWidth p β s K)*(sineWidth p β s K)⁻¹^k ≤
        M*Λ^(k+1)*((k+1).factorial:ℝ)^β := by
  have h2k : (2:WithTop ℕ) ≤ k := by exact_mod_cast hk
  have hp2 : (2:WithTop ℕ) ≤ p := h2k.trans hkp
  have hh := sineWidth_pos hp hβ hK hs hs1
  have hr := sineWidth_relative_small hp2 hτ hβ hK hs hs1 hsmall
  have hb := mul_le_mul_of_nonneg_right (F.source_derivative_coefficient hm hc hτ hs hh hr)
    (pow_nonneg (inv_nonneg.mpr hh.le) k)
  exact hb.trans (sineWidth_uniform_envelope hp
    (mul_nonneg (div_nonneg hm hc.le) (add_nonneg F.C₁_nonneg F.C₀_nonneg))
    hM hΛ hβ hK hs hs1 ht hscale ⟨by omega,hkp⟩)

variable {b : Budgets} {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s)
  (S : (F.sourceScaled hτ hs).Calibration b)

theorem source_objective_gradient (hamp : S.c*S.a = s^2/τ) (x : X) :
    gradient ((F.sourceScaled hτ hs).population S).objective x =
      s • (F.gA ((s/τ)⁻¹ • x)+
        deriv (SineLift.theta (S.a/S.h)) (F.B ((s/τ)⁻¹ • x)) • F.gB ((s/τ)⁻¹ • x)) := by
  rw [(F.sourceScaled hτ hs).population_objective_gradient S,hamp]
  change ((s^2/τ)/(s/τ)) • F.gA ((s/τ)⁻¹ • x)+
    ((s^2/τ)*deriv (SineLift.theta (S.a/S.h)) (F.B ((s/τ)⁻¹ • x))) •
      ((s/τ)⁻¹ • F.gB ((s/τ)⁻¹ • x)) = _
  have he : (s^2/τ)/(s/τ) = s := by field_simp; ring
  rw [he,smul_smul,smul_add,smul_smul]
  congr 1
  congr 1
  field_simp
  ring

theorem source_gradient_barrier (hamp : S.c*S.a = s^2/τ)
    (hsmall : |S.a/S.h| * F.C₀ ≤ 1/4)
    (hdist : 2*(S.a/S.h)^2*F.C₀^2*F.C₁ ≤ 1/4)
    (x : X) (hbar : (1/2:ℝ) ≤ ‖F.gA ((s/τ)⁻¹ • x)+F.gB ((s/τ)⁻¹ • x)‖) :
    s/4 ≤ ‖gradient ((F.sourceScaled hτ hs).population S).objective x‖ := by
  rw [F.source_objective_gradient hτ hs S hamp,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  let z := (s/τ)⁻¹ • x
  let d := deriv (SineLift.theta (S.a/S.h)) (F.B z)
  have ht : |d-1| ≤ 2*(S.a/S.h)^2*F.C₀^2 :=
    SineLift.theta_derivative_error (F.bound_B z) hsmall
  have hd : ‖F.gA z+d • F.gB z-(F.gA z+F.gB z)‖ ≤ 1/4 := by
    rw [show F.gA z+d • F.gB z-(F.gA z+F.gB z) = (d-1) • F.gB z by module,
      norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul ht (F.bound_gB z) (norm_nonneg _) (by positivity)).trans hdist
  have hn := norm_sub_le (F.gA z+d • F.gB z)
    (F.gA z+d • F.gB z-(F.gA z+F.gB z))
  rw [sub_sub_cancel] at hn
  have hb : (1/4:ℝ) ≤ ‖F.gA z+d • F.gB z‖ := by linarith
  exact (mul_le_mul_of_nonneg_left hb hs.le).trans_eq' (by ring)

theorem source_objective_gap (hamp : S.c*S.a = s^2/τ) (hzero : F.B 0 = 0)
    {G : ℝ} (hgap : ∀ w, F.A 0+F.B 0-(F.A w+F.B w) ≤ G) (x : X) :
    ((F.sourceScaled hτ hs).population S).objective 0-
      ((F.sourceScaled hτ hs).population S).objective x ≤ (s^2/τ)*(G+2*F.C₀) := by
  rw [(F.sourceScaled hτ hs).population_objective S]
  simp only [sourceScaled,scaled,smul_zero,hamp,hzero,SineLift.theta_zero,mul_zero,add_zero]
  let z := (s/τ)⁻¹ • x
  have hg := hgap z
  rw [hzero,add_zero] at hg
  have ht := (SineLift.abs_theta_le (S.a/S.h) (F.B z)).trans (F.bound_B z)
  have hb := (le_abs_self (F.B z)).trans (F.bound_B z)
  have hn := (neg_le_abs (SineLift.theta (S.a/S.h) (F.B z))).trans ht
  have hsum : F.A 0-F.A z-SineLift.theta (S.a/S.h) (F.B z) ≤ G+2*F.C₀ := by linarith
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ s^2/τ)).trans_eq' (by ring)

theorem source_initialized (hamp : S.c*S.a = s^2/τ) (hzero : F.B 0 = 0)
    {G : ℝ} (hgap : ∀ w, F.A 0+F.B 0-(F.A w+F.B w) ≤ G)
    (hbudget : (s^2/τ)*(G+2*F.C₀) ≤ b.Δ) :
    ((F.sourceScaled hτ hs).population S).Initialized 0 0 := by
  let P := (F.sourceScaled hτ hs).population S
  have hg : ∀ x, P.objective 0-P.objective x ≤ b.Δ := fun x =>
    (F.source_objective_gap hτ hs S hamp hzero hgap x).trans hbudget
  have hlo : ∀ y ∈ Set.range P.objective, P.objective 0-b.Δ ≤ y := by
    rintro y ⟨x,rfl⟩
    linarith [hg x]
  refine ⟨⟨P.objective 0-b.Δ,hlo⟩,?_,?_⟩
  · have hi := le_csInf (show (Set.range P.objective).Nonempty from ⟨P.objective 0,0,rfl⟩) hlo
    linarith
  · have hz : (F.sourceScaled hτ hs).B 0 = 0 := by simpa [sourceScaled,scaled] using hzero
    rw [(F.sourceScaled hτ hs).population_zero_inner S 0 hz,sub_self,norm_zero]
    exact b.R₀_nonneg

end Smoothness2601.SineGeometry.Profiles
