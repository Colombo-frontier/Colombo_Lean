import GradientHessian.LocalizedHigherDerivatives
import GradientHessian.LocalizedNormDerivatives
import GradientHessian.LocalizedBounds

/-! Actual global tensor bounds for the literal localized perturbation and
incoming coefficient. The constants depend only on the fixed septic profile.
This completes the product-rule part of `lem:localized-bounds`. -/

noncomputable section
open Set Filter Bornology
open scoped Topology BigOperators InnerProductSpace

namespace GradientHessian.LocalizedProductDerivatives
open Localized LocalizedHigherDerivatives LocalizedNormDerivatives RadialHigherDerivatives

def bracketConstant (n : ℕ) : ℝ := if n = 0 then 208 else 8*32^n+48

theorem bracketConstant_pos (n : ℕ) : 0 < bracketConstant n := by
  unfold bracketConstant
  split_ifs <;> positivity

def perturbationConstant (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    cutoffConstant 4 5 i * bracketConstant (n-i)

theorem perturbationConstant_pos (n : ℕ) : 0 < perturbationConstant n := by
  have hs : 0 ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
      cutoffConstant 4 5 i * bracketConstant (n-i) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (cutoffConstant_pos _ _ _).le)
      (bracketConstant_pos _).le
  unfold perturbationConstant
  linarith

section Normed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_sub_le {n : ℕ} {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y-g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := by
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' hf hg.neg]
  change ‖iteratedFDeriv ℝ n f x + iteratedFDeriv ℝ n (-g) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply]
  exact (norm_add_le _ _).trans_eq (by rw [norm_neg])

theorem iteratedFDeriv_add_const_of_pos {n : ℕ} (hn : 1 ≤ n) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) (d : F) :
    iteratedFDeriv ℝ n (fun y => f y+d) x = iteratedFDeriv ℝ n f x := by
  rw [iteratedFDeriv_add_apply' hf contDiffAt_const]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, add_zero]

end Normed

theorem radius_power_antitone {w R : ℝ} (hw : 0 < w) (hwR : w ≤ R) {n : ℕ}
    (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) : R^(1-(n:ℤ)) ≤ w^(1-(n:ℤ)) := by
  have hR := hw.trans_le hwR
  interval_cases n
  · norm_num
  · norm_num
    exact inv_anti₀ hw hwR
  · norm_num [zpow_neg]
    exact inv_anti₀ (sq_pos_of_pos hw) (pow_le_pow_left₀ hw.le hwR 2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem well_contDiff (R w : ℝ) (c : E) (n : WithTop ℕ∞) :
    ContDiff ℝ n (well R w c) :=
  contDiff_const.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

theorem cutoff_contDiff (w : ℝ) (c : E) : ContDiff ℝ 3 (cutoff w c) :=
  contDiff_const.sub (Profiles.contDiff_step.comp
    ((((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).div_const _))

theorem perturbation_contDiff {R : ℝ} (hR : 0 < R) (w : ℝ) (c : E) :
    ContDiff ℝ 3 (perturbation R w c) :=
  (cutoff_contDiff w c).mul ((well_contDiff R w c 3).sub (publicPotential_contDiff hR 3))

theorem scaled_norm_sq_derivative_bound {w : ℝ} (hw : 0 < w) {n : ℕ}
    (hn : 1 ≤ n) (c u : E) (hu : ‖u-c‖ ≤ 3*w) :
    ‖iteratedFDeriv ℝ n (fun x : E => ‖w⁻¹ • (x-c)‖^2) u‖ ≤ 32^n*(w⁻¹)^n := by
  let A : E →L[ℝ] E := w⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ w⁻¹ := by
    dsimp only [A]
    rw [norm_smul w⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hw.le) ContinuousLinearMap.norm_id_le
  have hx : ‖A (u-c)‖ ≤ 4 := by
    change ‖w⁻¹ • (u-c)‖ ≤ 4
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw), inv_mul_eq_div,
      div_le_iff₀ hw]
    linarith
  change ‖iteratedFDeriv ℝ n (fun x => ((fun y : E => ‖y‖^2) ∘ A) (x-c)) u‖ ≤ _
  rw [iteratedFDeriv_comp_sub, A.iteratedFDeriv_comp_right (contDiff_norm_sq ℝ) (u-c) le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun y : E => ‖y‖^2) (A (u-c))‖ * ‖A‖^n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (fun y : E => ‖y‖^2) (A (u-c))).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ 32^n*(w⁻¹)^n := by
      apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity) (by positivity)
      simpa only [real_inner_self_eq_norm_sq] using norm_iteratedFDeriv_inner_self_le hx n hn

theorem well_derivative_bound_on_ball {R w : ℝ} (hw : 0 < w) {n : ℕ}
    (hn : 1 ≤ n) (c u : E) (hu : ‖u-c‖ ≤ 3*w) :
    ‖iteratedFDeriv ℝ n (well R w c) u‖ ≤ (8*32^n)*w^(1-(n:ℤ)) := by
  let f : E → ℝ := fun x => ‖w⁻¹ • (x-c)‖^2
  have hf : ContDiff ℝ n f :=
    ((contDiff_const.smul (contDiff_id.sub contDiff_const)).norm_sq ℝ)
  have heq : well R w c = fun x => (8*w) • f x + (publicPotential R c-160*w) := by
    funext x
    simp only [well, f, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw), smul_eq_mul]
    field_simp
    ring
  rw [heq, iteratedFDeriv_add_const_of_pos hn (hf.const_smul (8*w)).contDiffAt,
    iteratedFDeriv_const_smul_apply' hf.contDiffAt,
    norm_smul (8*w) (iteratedFDeriv ℝ n f u), Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 8*w)]
  calc
    _ ≤ (8*w)*(32^n*(w⁻¹)^n) := mul_le_mul_of_nonneg_left
      (scaled_norm_sq_derivative_bound hw hn c u hu) (by positivity)
    _ = (8*32^n)*w^(1-(n:ℤ)) := by
      rw [zpow_sub₀ hw.ne', zpow_one, zpow_natCast, div_eq_mul_inv, ← inv_pow]
      ring

variable [CompleteSpace E]

theorem bracket_derivative_bound_on_ball {R w : ℝ} (hw : 0 < w) (hwR : w ≤ R)
    {n : ℕ} (hn : n ≤ 3) (c u : E) (hu : ‖u-c‖ ≤ 3*w) :
    ‖iteratedFDeriv ℝ n (fun x => well R w c x-publicPotential R x) u‖ ≤
      bracketConstant n*w^(1-(n:ℤ)) := by
  have hR := hw.trans_le hwR
  by_cases hn₀ : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    simp only [bracketConstant, ↓reduceIte, Nat.cast_zero, sub_zero, zpow_one]
    obtain ⟨hl, hu'⟩ := well_difference_bounds hR hw c u hu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hn₁ : 1 ≤ n := by omega
    have h := norm_iteratedFDeriv_sub_le (well_contDiff R w c n).contDiffAt
      (publicPotential_contDiff hR n).contDiffAt (x := u)
    calc
      _ ≤ ‖iteratedFDeriv ℝ n (well R w c) u‖ +
          ‖iteratedFDeriv ℝ n (publicPotential R : E → ℝ) u‖ := h
      _ ≤ (8*32^n)*w^(1-(n:ℤ)) + 48*R^(1-(n:ℤ)) :=
        add_le_add (well_derivative_bound_on_ball hw hn₁ c u hu)
          (publicPotential_derivative_bound hR hn₁ hn u)
      _ ≤ (8*32^n)*w^(1-(n:ℤ)) + 48*w^(1-(n:ℤ)) := by
        gcongr
        exact radius_power_antitone hw hwR hn₁ hn
      _ = bracketConstant n*w^(1-(n:ℤ)) := by simp only [bracketConstant, if_neg hn₀]; ring

theorem perturbation_derivative_bound {R w : ℝ} (hw : 0 < w) (hwR : w ≤ R)
    {n : ℕ} (hn : n ≤ 3) (c u : E) :
    ‖iteratedFDeriv ℝ n (perturbation R w c) u‖ ≤ perturbationConstant n*w^(1-(n:ℤ)) := by
  have hR := hw.trans_le hwR
  by_cases hu : ‖u-c‖ ≤ 3*w
  · have hb : ContDiff ℝ 3 (fun x => well R w c x-publicPotential R x) :=
      (well_contDiff R w c 3).sub (publicPotential_contDiff hR 3)
    have h := norm_iteratedFDeriv_mul_le (cutoff_contDiff w c) hb u
      (n := n) (by exact_mod_cast hn)
    apply h.trans
    calc
      _ ≤ ∑ i ∈ Finset.range (n+1), ((n.choose i : ℝ)*cutoffConstant 4 5 i*
          bracketConstant (n-i))*w^(1-(n:ℤ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hni : n-i ≤ 3 := (Nat.sub_le n i).trans hn
        have hi₃ : i ≤ 3 := hin.trans hn
        have hmul := mul_le_mul
          (mul_le_mul_of_nonneg_left (cutoff_higher_derivative_bound hw i hi₃ c u)
            (Nat.cast_nonneg (n.choose i)))
          (bracket_derivative_bound_on_ball hw hwR hni c u hu)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
            (div_nonneg (cutoffConstant_pos _ _ _).le (pow_nonneg hw.le _)))
        apply hmul.trans_eq
        rw [div_eq_mul_inv, ← zpow_natCast w i, ← zpow_neg]
        calc
          _ = ((n.choose i : ℝ)*cutoffConstant 4 5 i*bracketConstant (n-i))*
              (w^(-(i:ℤ))*w^(1-((n-i:ℕ):ℤ))) := by ring
          _ = _ := by
            have he : -(i:ℤ)+(1-((n-i:ℕ):ℤ)) = 1-(n:ℤ) := by
              rw [Nat.cast_sub hin]
              ring
            rw [← zpow_add₀ hw.ne', he]
      _ = (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*cutoffConstant 4 5 i*
          bracketConstant (n-i))*w^(1-(n:ℤ)) := by rw [Finset.sum_mul]
      _ ≤ perturbationConstant n*w^(1-(n:ℤ)) := by
        apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hw.le _)
        exact le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
  · have heq : perturbation R w c =ᶠ[𝓝 u] (fun _ => 0) := by
      have he : ∀ᶠ x : E in 𝓝 u, 3*w < ‖x-c‖ :=
        (continuous_id.sub continuous_const).norm.continuousAt.eventually
          (lt_mem_nhds (lt_of_not_ge hu))
      filter_upwards [he] with x hx
      exact perturbation_eq_zero_of_three_mul_le_norm hw hx.le
    rw [iteratedFDeriv_eq_of_eventuallyEq heq n, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact mul_nonneg (perturbationConstant_pos n).le (zpow_nonneg hw.le _)

theorem potential_derivative_bound {R w : ℝ} (hw : 0 < w) (hwR : w ≤ R)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) (c u : E) :
    ‖iteratedFDeriv ℝ n (potential R w c) u‖ ≤
      (48+perturbationConstant n)*w^(1-(n:ℤ)) := by
  have hR := hw.trans_le hwR
  have hψ : ContDiff ℝ n (perturbation R w c) :=
    (perturbation_contDiff hR w c).of_le (by exact_mod_cast hn₃)
  unfold potential
  rw [iteratedFDeriv_add_apply' (publicPotential_contDiff hR n).contDiffAt hψ.contDiffAt]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (publicPotential R : E → ℝ) u‖ +
        ‖iteratedFDeriv ℝ n (perturbation R w c) u‖ := norm_add_le _ _
    _ ≤ 48*R^(1-(n:ℤ)) + perturbationConstant n*w^(1-(n:ℤ)) :=
      add_le_add (publicPotential_derivative_bound hR hn₁ hn₃ u)
        (perturbation_derivative_bound hw hwR hn₃ c u)
    _ ≤ 48*w^(1-(n:ℤ)) + perturbationConstant n*w^(1-(n:ℤ)) := by
      gcongr
      exact radius_power_antitone hw hwR hn₁ hn₃
    _ = _ := by ring

theorem incoming_derivative_bound {R w : ℝ} (hw : 0 < w) (hwR : w ≤ R)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) (c u : E) :
    ‖iteratedFDeriv ℝ n (incoming R w c) u‖ ≤
      (96+perturbationConstant n)*w^(1-(n:ℤ)) := by
  have hR := hw.trans_le hwR
  have hV : ContDiff ℝ n (potential R w c) :=
    (localized_contDiff hR hw c).1.of_le (by exact_mod_cast hn₃)
  unfold incoming
  rw [iteratedFDeriv_add_const_of_pos hn₁ (hV.sub (drive_contDiff hw c n)).contDiffAt]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (potential R w c) u‖ +
        ‖iteratedFDeriv ℝ n (drive w c) u‖ :=
      norm_iteratedFDeriv_sub_le hV.contDiffAt (drive_contDiff hw c n).contDiffAt
    _ ≤ (48+perturbationConstant n)*w^(1-(n:ℤ)) + 48*w^(1-(n:ℤ)) :=
      add_le_add (potential_derivative_bound hw hwR hn₁ hn₃ c u)
        (drive_derivative_bound hw hn₁ hn₃ c u)
    _ = _ := by ring

/-- One absolute constant shared by all orders and all localized profiles. -/
def localizedConstant : ℝ := 97 +
  (∑ i ∈ Finset.range 4, perturbationConstant i) +
  ∑ i ∈ Finset.range 4, cutoffConstant 1 3 i

theorem localizedConstant_bounds {n : ℕ} (hn : n ≤ 3) :
    96+perturbationConstant n ≤ localizedConstant ∧
      cutoffConstant 1 3 n ≤ localizedConstant := by
  have hm : n ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hψ₀ : 0 ≤ ∑ i ∈ Finset.range 4, perturbationConstant i :=
    Finset.sum_nonneg (fun i _ => (perturbationConstant_pos i).le)
  have hχ₀ : 0 ≤ ∑ i ∈ Finset.range 4, cutoffConstant 1 3 i :=
    Finset.sum_nonneg (fun i _ => (cutoffConstant_pos 1 3 i).le)
  have hψ : perturbationConstant n ≤ ∑ i ∈ Finset.range 4, perturbationConstant i :=
    Finset.single_le_sum (fun i _ => (perturbationConstant_pos i).le) hm
  have hχ : cutoffConstant 1 3 n ≤ ∑ i ∈ Finset.range 4, cutoffConstant 1 3 i :=
    Finset.single_le_sum (fun i _ => (cutoffConstant_pos 1 3 i).le) hm
  unfold localizedConstant
  constructor <;> linarith

theorem localizedConstant_ge_48 : 48 ≤ localizedConstant := by
  have h := (localizedConstant_bounds (n := 0) (by norm_num)).1
  have hp := perturbationConstant_pos 0
  linarith

theorem localizedConstant_pos : 0 < localizedConstant := by
  have h := localizedConstant_ge_48
  linarith

/-- A literal bundle of the assertions of `lem:localized-bounds`.
All derivative fields refer to the actual iterated Frechet derivatives. -/
structure LocalizedBounds (R w : ℝ) (c : E) : Prop where
  smooth_public : ContDiff ℝ 3 (publicPotential R : E → ℝ)
  smooth_drive : ContDiff ℝ 3 (drive w c)
  smooth_well : ContDiff ℝ 3 (well R w c)
  smooth_cutoff : ContDiff ℝ 3 (cutoff w c)
  smooth_perturbation : ContDiff ℝ 3 (perturbation R w c)
  smooth_potential : ContDiff ℝ 3 (potential R w c)
  smooth_incoming : ContDiff ℝ 3 (incoming R w c)
  smooth_port : ContDiff ℝ 3 (port w c)
  perturbation_values : ∀ u, -208*w ≤ perturbation R w c u ∧ perturbation R w c u ≤ 0
  incoming_values : ∀ u, 256*R ≤ incoming R w c u ∧ incoming R w c u ≤ 768*R
  perturbation_derivatives : ∀ n ≤ 3, ∀ u,
    ‖iteratedFDeriv ℝ n (perturbation R w c) u‖ ≤ localizedConstant*w^(1-(n:ℤ))
  port_derivatives : ∀ n, 1 ≤ n → n ≤ 3 → ∀ u,
    ‖iteratedFDeriv ℝ n (port w c) u‖ ≤ localizedConstant/w^n
  incoming_derivatives : ∀ n, 1 ≤ n → n ≤ 3 → ∀ u,
    ‖iteratedFDeriv ℝ n (incoming R w c) u‖ ≤ localizedConstant*w^(1-(n:ℤ))
  public_nonneg : ∀ u : E, 0 ≤ publicPotential R u
  public_zero : publicPotential R (0:E) = 0
  public_coercive : Tendsto (publicPotential R : E → ℝ) (cobounded E) atTop
  public_derivatives : ∀ n, 1 ≤ n → n ≤ 3 → ∀ u : E,
    ‖iteratedFDeriv ℝ n (publicPotential R : E → ℝ) u‖ ≤ localizedConstant*R^(1-(n:ℤ))
  cancellation : ∀ u, potential R w c u-incoming R w c u = drive w c u-512*R

/-- The full localized-bounds lemma. The source's Euclidean assumptions
`R ≥ 16 w ≥ 16` and `c = R v`, `‖v‖ = 1`, imply these weaker hypotheses. -/
theorem localized_bounds {R w : ℝ} (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : E) (hc : ‖c‖ = R) : LocalizedBounds R w c := by
  have hwR : w ≤ R := by linarith
  have hR := hw.trans_le hwR
  have hsm := localized_contDiff hR hw c
  refine {
    smooth_public := publicPotential_contDiff hR 3
    smooth_drive := drive_contDiff hw c 3
    smooth_well := well_contDiff R w c 3
    smooth_cutoff := cutoff_contDiff w c
    smooth_perturbation := perturbation_contDiff hR w c
    smooth_potential := hsm.1
    smooth_incoming := hsm.2.1
    smooth_port := hsm.2.2
    perturbation_values := perturbation_bounds hR hw c
    incoming_values := fun u => incoming_bounds hw hscale c u hc
    perturbation_derivatives := ?_
    port_derivatives := ?_
    incoming_derivatives := ?_
    public_nonneg := publicPotential_nonneg hR.le
    public_zero := publicPotential_zero hR.le
    public_coercive := publicPotential_coercive R
    public_derivatives := ?_
    cancellation := Localized.cancellation R w c }
  · intro n hn u
    apply (perturbation_derivative_bound hw hwR hn c u).trans
    apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hw.le _)
    have h := (localizedConstant_bounds hn).1
    linarith
  · intro n _ hn u
    apply (port_higher_derivative_bound hw n hn c u).trans
    exact div_le_div_of_nonneg_right (localizedConstant_bounds hn).2 (pow_nonneg hw.le n)
  · intro n hn₁ hn₃ u
    apply (incoming_derivative_bound hw hwR hn₁ hn₃ c u).trans
    exact mul_le_mul_of_nonneg_right (localizedConstant_bounds hn₃).1 (zpow_nonneg hw.le _)
  · intro n hn₁ hn₃ u
    apply (publicPotential_derivative_bound hR hn₁ hn₃ u).trans
    exact mul_le_mul_of_nonneg_right localizedConstant_ge_48 (zpow_nonneg hR.le _)

end GradientHessian.LocalizedProductDerivatives
