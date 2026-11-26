import MatchingBounds1005.PathGreen
import MatchingBounds1005.BlockGradientBound

/-! Quantitative readout and inverse estimates for the concrete path data. -/
noncomputable section
open scoped Matrix BigOperators InnerProductSpace

namespace MatchingBounds1005.PathGreen

theorem suffix_card_formula (n : ℕ) :
    (suffixSet n).card = n + 2 - (n + 2) / 2 := by
  let first : Fin (n + 1) := ⟨(n + 2) / 2 - 1, by omega⟩
  have hset : suffixSet n = Finset.Ici first := by
    ext i
    simp only [suffixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    change (n + 2) / 2 ≤ i.val + 1 ↔ (n + 2) / 2 - 1 ≤ i.val
    omega
  rw [hset, Fin.card_Ici]
  dsimp [first]
  omega

theorem suffix_card_twice (n : ℕ) : n + 1 ≤ 2 * (suffixSet n).card := by
  rw [suffix_card_formula]
  omega

theorem scaled_suffix_card (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ h * ((suffixSet (pathEdges h)).card : ℝ) := by
  have hs := (ceiling_scale h hh hhsmall).2.2.1
  have hc : ((pathEdges h + 1 : ℕ) : ℝ) ≤ 2 * ((suffixSet (pathEdges h)).card : ℝ) := by
    exact_mod_cast suffix_card_twice (pathEdges h)
  have hm := mul_le_mul_of_nonneg_left hc hh.le
  nlinarith only [hs, hm]

theorem suffixFunction_sum (A : ℝ) (n : ℕ) :
    (∑ i, suffixFunction A n i) = A * Real.sqrt ((suffixSet n).card : ℝ) := by
  have hs : (0 : ℝ) < (suffixSet n).card := by exact_mod_cast suffix_card_pos n
  have hsqrt : 0 < Real.sqrt ((suffixSet n).card : ℝ) := Real.sqrt_pos.mpr hs
  have hdiv : ((suffixSet n).card : ℝ) / Real.sqrt ((suffixSet n).card : ℝ) =
      Real.sqrt ((suffixSet n).card : ℝ) := by
    apply (div_eq_iff hsqrt.ne').mpr
    nlinarith only [Real.sq_sqrt hs.le]
  calc
    _ = ((suffixSet n).card : ℝ) * (A / Real.sqrt ((suffixSet n).card : ℝ)) := by
      simp [suffixFunction, Finset.sum_ite]
    _ = A * (((suffixSet n).card : ℝ) / Real.sqrt ((suffixSet n).card : ℝ)) := by ring
    _ = _ := by rw [hdiv]

theorem weighted_matrix_lower {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (c : ℝ)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, c ≤ M i j) :
    c * (∑ i, a i) ^ 2 ≤ dotProduct a (M *ᵥ a) := by
  have hexpand : c * (∑ i, a i) ^ 2 = ∑ i, ∑ j, c * a i * a j := by
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum, mul_assoc]
  rw [hexpand]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hm := mul_le_mul_of_nonneg_right (hc i j) (mul_nonneg (ha i) (ha j))
  nlinarith only [hm]

theorem beta_le_of_coercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : BlockGeometry E) (γ : ℝ) (hγ : 0 < γ)
    (hcoercive : ∀ x, γ * ‖x‖ ^ 2 ≤ ⟪x, G.H x⟫_ℝ) :
    G.beta ≤ ‖G.a‖ ^ 2 / γ := by
  have hc := hcoercive (G.Hinv G.a)
  rw [G.inverse, real_inner_comm G.a (G.Hinv G.a)] at hc
  change γ * ‖G.Hinv G.a‖ ^ 2 ≤ G.beta at hc
  have hinner := abs_real_inner_le_norm G.a (G.Hinv G.a)
  change |G.beta| ≤ ‖G.a‖ * ‖G.Hinv G.a‖ at hinner
  have hsq := (sq_le_sq₀ (abs_nonneg G.beta)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
  rw [sq_abs, mul_pow] at hsq
  have hsq' := mul_le_mul_of_nonneg_left hsq hγ.le
  have hc' := mul_le_mul_of_nonneg_left hc (sq_nonneg ‖G.a‖)
  have hcore : γ * G.beta ≤ ‖G.a‖ ^ 2 := by
    have hb : 0 < G.beta := G.beta_pos
    apply (mul_le_mul_right hb).mp
    nlinarith only [hsq', hc']
  apply (le_div_iff₀ hγ).mpr
  nlinarith only [hcore]

section Actual

variable (L h A : ℝ) (hL : 0 < L) (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (hA : 0 < A)

local notation "G₀" => actualBlockGeometry L h A hL hh hhsmall hA
local notation "n₀" => pathEdges h

theorem actual_alpha_lower : A * Real.sqrt ((suffixSet (pathEdges h)).card : ℝ) / (9 * L * h) ≤ (G₀).alpha := by
  have hm : (1 / (9 * L * h)) * (∑ i, suffixFunction A n₀ i) ≤
      ∑ i, (pathMatrix L h n₀)⁻¹ i 0 * suffixFunction A n₀ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (pathMatrix_inverse_bounds L h hL hh hhsmall i 0).1.le
      (suffixFunction_nonneg A hA.le n₀ i)
  rw [suffixFunction_sum] at hm
  change _ ≤ ⟪suffixVector A n₀, ((pathMatrix L h n₀)⁻¹).toEuclideanLin (entryVector n₀)⟫_ℝ
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change _ ≤ dotProduct (((pathMatrix L h n₀)⁻¹) *ᵥ (Pi.single 0 1)) (suffixFunction A n₀)
  rw [Matrix.mulVec_single_one]
  convert hm using 1
  ring

theorem actual_beta_suffix_lower : A ^ 2 * ((suffixSet (pathEdges h)).card : ℝ) / (9 * L * h) ≤ (G₀).beta := by
  have hm := weighted_matrix_lower ((pathMatrix L h n₀)⁻¹) (1 / (9 * L * h))
    (suffixFunction A n₀) (suffixFunction_nonneg A hA.le n₀)
    (fun i j => (pathMatrix_inverse_bounds L h hL hh hhsmall i j).1.le)
  rw [suffixFunction_sum, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ((suffixSet (pathEdges h)).card : ℝ))] at hm
  change _ ≤ ⟪suffixVector A n₀, ((pathMatrix L h n₀)⁻¹).toEuclideanLin (suffixVector A n₀)⟫_ℝ
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  convert hm using 1
  ring

theorem actual_beta_lower : A ^ 2 / (18 * (L * h ^ 2)) ≤ (G₀).beta := by
  have hc := scaled_suffix_card h hh hhsmall
  have hb := actual_beta_suffix_lower L h A hL hh hhsmall hA
  have hd : 0 < 9 * L * h := by positivity
  have hb' := (div_le_iff₀ hd).mp hb
  apply (div_le_iff₀ (by positivity : 0 < 18 * (L * h ^ 2))).mpr
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg A)
  have hm' := mul_le_mul_of_nonneg_left hb' hh.le
  nlinarith only [hm, hm']

theorem actual_beta_upper : (G₀).beta ≤ A ^ 2 / (L * h ^ 2) := by
  have hb := beta_le_of_coercive G₀ (L * h ^ 2) (by positivity)
    (actualBlockGeometry_coercive L h A hL hh hhsmall hA)
  change (G₀).beta ≤ ‖suffixVector A n₀‖ ^ 2 / (L * h ^ 2) at hb
  rwa [suffixVector_norm A hA.le n₀] at hb

theorem actual_rho_upper : (G₀).rho ≤ 16 / (L * h) := by
  change ⟪entryVector n₀, ((pathMatrix L h n₀)⁻¹).toEuclideanLin (entryVector n₀)⟫_ℝ ≤ _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change dotProduct (((pathMatrix L h n₀)⁻¹) *ᵥ (Pi.single 0 1)) (Pi.single 0 1) ≤ _
  rw [Matrix.mulVec_single_one, dotProduct_single, mul_one]
  exact (pathMatrix_inverse_bounds L h hL hh hhsmall 0 0).2

theorem actual_alpha_squared_lower : A ^ 2 / (162 * L ^ 2 * h ^ 3) ≤ (G₀).alpha ^ 2 := by
  have ha := actual_alpha_lower L h A hL hh hhsmall hA
  have ha' := (div_le_iff₀ (by positivity : 0 < 9 * L * h)).mp ha
  have hapos : 0 < (G₀).alpha := (G₀).alpha_pos
  have hs : 0 ≤ ((suffixSet (pathEdges h)).card : ℝ) := by positivity
  have hasq := (sq_le_sq₀ (by positivity : 0 ≤ A * Real.sqrt ((suffixSet (pathEdges h)).card : ℝ))
    (by positivity : 0 ≤ (G₀).alpha * (9 * L * h))).2 ha'
  rw [mul_pow, Real.sq_sqrt hs] at hasq
  have hm := mul_le_mul_of_nonneg_left hasq (by positivity : 0 ≤ 2 * h)
  have hc := mul_le_mul_of_nonneg_left (scaled_suffix_card h hh hhsmall) (sq_nonneg A)
  apply (div_le_iff₀ (by positivity : 0 < 162 * L ^ 2 * h ^ 3)).mpr
  nlinarith only [hm, hc]

theorem actual_kappa_upper : (G₀).kappa ≤ 2592 * (L * h ^ 2) / A ^ 2 := by
  have ha := actual_alpha_squared_lower L h A hL hh hhsmall hA
  have hr := actual_rho_upper L h A hL hh hhsmall hA
  change (G₀).rho / (G₀).alpha ^ 2 ≤ _
  calc
    _ ≤ (16 / (L * h)) / (G₀).alpha ^ 2 :=
      div_le_div_of_nonneg_right hr (sq_nonneg _)
    _ ≤ (16 / (L * h)) / (A ^ 2 / (162 * L ^ 2 * h ^ 3)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) ha
    _ = _ := by field_simp; ring

theorem actual_lambda_squared_bound : ((G₀).lam * A) ^ 2 ≤ 162 * L ^ 2 * h ^ 3 := by
  have ha := actual_alpha_squared_lower L h A hL hh hhsmall hA
  have ha' := (div_le_iff₀ (by positivity : 0 < 162 * L ^ 2 * h ^ 3)).mp ha
  have hm := mul_le_mul_of_nonneg_left ha' (sq_nonneg (G₀).lam)
  have hid : (G₀).lam ^ 2 * ((G₀).alpha ^ 2 * (162 * L ^ 2 * h ^ 3)) =
      162 * L ^ 2 * h ^ 3 := by
    calc
      _ = ((G₀).lam * (G₀).alpha) ^ 2 * (162 * L ^ 2 * h ^ 3) := by ring
      _ = _ := by rw [(G₀).lam_mul_alpha]; ring
  rw [hid] at hm
  nlinarith only [hm]

theorem actual_coupling_bound :
    2 * (G₀).lam * A ≤ 18 * Real.sqrt 2 * L * h * Real.sqrt h := by
  have hl := actual_lambda_squared_bound L h A hL hh hhsmall hA
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsh := Real.sq_sqrt hh.le
  have hrhs : (18 * Real.sqrt 2 * L * h * Real.sqrt h) ^ 2 =
      648 * L ^ 2 * h ^ 3 := by
    calc
      _ = 324 * (Real.sqrt 2) ^ 2 * L ^ 2 * h ^ 2 * (Real.sqrt h) ^ 2 := by ring
      _ = _ := by rw [hs2, hsh]; ring
  have hlpos := (G₀).lam_nonneg
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [hrhs]
  nlinarith only [hl]

theorem actual_tau_bounds :
    L * h ^ 2 / A ^ 2 ≤ (G₀).tau ∧ (G₀).tau ≤ 18 * (L * h ^ 2) / A ^ 2 := by
  have hb := actual_beta_lower L h A hL hh hhsmall hA
  have hb' := actual_beta_upper L h A hL hh hhsmall hA
  have hta : (G₀).tau * (G₀).beta = 1 := inv_mul_cancel₀ (G₀).beta_ne
  have ht := (G₀).tau_nonneg
  have hx := mul_le_mul_of_nonneg_left ((le_div_iff₀ (by positivity)).mp hb') ht
  have hy := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).mp hb) ht
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
    calc
      _ = (G₀).tau * ((G₀).beta * (L * h ^ 2)) := by rw [← mul_assoc, hta, one_mul]
      _ ≤ _ := hx
  · apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
    calc
      _ ≤ (G₀).tau * ((G₀).beta * (18 * (L * h ^ 2))) := hy
      _ = _ := by rw [← mul_assoc, hta, one_mul]

theorem actual_gradient_coefficient :
    L * h ^ 2 / (208 * A) ≤ Real.sqrt (L * h ^ 2) /
      (4 * (Real.sqrt (G₀).beta + (G₀).beta * Real.sqrt (G₀).rho / (G₀).alpha)) := by
  let γ := L * h ^ 2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hb : 0 < (G₀).beta := (G₀).beta_pos
  have ha : 0 < (G₀).alpha := (G₀).alpha_pos
  have hk : 0 ≤ (G₀).kappa := (G₀).kappa_nonneg
  have hβγ : (G₀).beta * γ ≤ A ^ 2 :=
    (le_div_iff₀ hγ).mp (actual_beta_upper L h A hL hh hhsmall hA)
  have hκA : (G₀).kappa * A ^ 2 ≤ 2592 * γ :=
    (le_div_iff₀ (sq_pos_of_pos hA)).mp (actual_kappa_upper L h A hL hh hhsmall hA)
  have hfirst : Real.sqrt γ * Real.sqrt (G₀).beta ≤ A := by
    apply (sq_le_sq₀ (by positivity) hA.le).mp
    rw [mul_pow, Real.sq_sqrt hγ.le, Real.sq_sqrt hb.le]
    nlinarith only [hβγ]
  have hsecond₁ : A * Real.sqrt (G₀).kappa ≤ 51 * Real.sqrt γ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hk, Real.sq_sqrt hγ.le]
    nlinarith only [hκA, hγ]
  have hsecond : Real.sqrt γ * (G₀).beta * Real.sqrt (G₀).kappa ≤ 51 * A := by
    apply (mul_le_mul_left hA).mp
    calc
      _ = ((G₀).beta * Real.sqrt γ) * (A * Real.sqrt (G₀).kappa) := by ring
      _ ≤ ((G₀).beta * Real.sqrt γ) * (51 * Real.sqrt γ) :=
        mul_le_mul_of_nonneg_left hsecond₁ (by positivity)
      _ = 51 * ((G₀).beta * γ) := by
        calc
          _ = 51 * (G₀).beta * (Real.sqrt γ) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hγ.le]; ring
      _ ≤ 51 * A ^ 2 := mul_le_mul_of_nonneg_left hβγ (by norm_num)
      _ = _ := by ring
  have hrootκ : Real.sqrt (G₀).kappa = Real.sqrt (G₀).rho / (G₀).alpha := by
    change Real.sqrt ((G₀).rho / (G₀).alpha ^ 2) = _
    rw [Real.sqrt_div (G₀).rho_nonneg, Real.sqrt_sq ha.le]
  rw [hrootκ] at hsecond
  let D := Real.sqrt (G₀).beta + (G₀).beta * Real.sqrt (G₀).rho / (G₀).alpha
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : Real.sqrt γ * D ≤ 52 * A := by
    dsimp [D]
    calc
      _ = Real.sqrt γ * Real.sqrt (G₀).beta +
          Real.sqrt γ * (G₀).beta * (Real.sqrt (G₀).rho / (G₀).alpha) := by ring
      _ ≤ A + 51 * A := add_le_add hfirst hsecond
      _ = _ := by ring
  change γ / (208 * A) ≤ Real.sqrt γ / (4 * D)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ = (4 * Real.sqrt γ) * (Real.sqrt γ * D) := by
      calc
        _ = 4 * (Real.sqrt γ) ^ 2 * D := by rw [Real.sq_sqrt hγ.le]; ring
        _ = _ := by ring
    _ ≤ (4 * Real.sqrt γ) * (52 * A) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The numerical zero-tail certificate for the actual path-matrix objective. -/
theorem actual_gradient_bound (r : ℝ) (hr : 1 ≤ r) (n : ℕ)
    (z : BlockGeometry.BlockSpace (E := EuclideanSpace ℝ (Fin (n₀ + 1))) n)
    (htail : ⟪(G₀).a, z (Fin.last n)⟫_ℝ = 0) :
    L * h ^ 2 / (208 * A) ≤ ‖gradient ((G₀).euclideanObjective r n) z‖ := by
  exact (actual_gradient_coefficient L h A hL hh hhsmall hA).trans
    ((G₀).block_gradient_certificate r hr n z htail (L * h ^ 2) (by positivity)
      (actualBlockGeometry_coercive L h A hL hh hhsmall hA))

end Actual
end MatchingBounds1005.PathGreen

