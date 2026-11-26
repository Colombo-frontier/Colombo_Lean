import Bilevel.ZeroChainFlatteningMap

/-! Sharp scale dependence of the actual flattened residual derivatives. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainFlatteningBounds
open ZeroChain ZeroChainResidual ZeroChainResidualLocality ZeroChainResidualScaled
  ZeroChainFlatteningCutoff ZeroChainFlatteningMap

def flattenedResidual (n : ℕ) (a β δ : ℝ) (z : Space n) : ℝ := R n a β (flattenMap n δ z)

theorem flattenedResidual_contDiff (n : ℕ) (a β δ : ℝ) : ContDiff ℝ 3 (flattenedResidual n a β δ) :=
  (R_contDiff n a β).comp (flattenMap_contDiff n δ)

theorem linear_scale_jet_le {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (s : ℝ) (z : Space n) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun w => f (s • w)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (s • z)‖*|s|^k := by
  let g : Space n →L[ℝ] Space n := s • ContinuousLinearMap.id ℝ (Space n)
  have hg : ‖g‖ ≤ |s| := by
    apply ContinuousLinearMap.opNorm_le_bound g (abs_nonneg _)
    intro v
    change ‖s • v‖ ≤ |s| * ‖v‖
    simp only [norm_smul, Real.norm_eq_abs, le_refl]
  change ‖iteratedFDeriv ℝ k (f ∘ g) z‖ ≤ _
  rw [g.iteratedFDeriv_comp_right hf z (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg _) (norm_nonneg _)

theorem jet_sub_const {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (c : ℝ) (z : Space n) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (fun w => f w-c) z = iteratedFDeriv ℝ k f z := by
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' (hf.of_le hk').contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (show k ≠ 0 by omega), Pi.zero_apply, add_zero]

/-- Subtracting a constant at the evaluation point before applying the
composition estimate retains the required δ^(1-k) dependence. -/
theorem flatten_positive_jet_bound {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (K M δ : ℝ) (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hcore : ∀ (j : ℕ), 1 ≤ j → j ≤ 3 → ∀ w : Space n, ‖iteratedFDeriv ℝ j (coreMap n) w‖ ≤ K)
    (houter : ∀ (j : ℕ), 1 ≤ j → j ≤ 3 → ∀ w : Space n,
      ‖iteratedFDeriv ℝ j f w‖ ≤ M*δ/δ^j)
    (z : Space n) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun w => f (flattenMap n δ w)) z‖ ≤
      (k.factorial:ℝ)*M*K^k*δ/δ^k := by
  let x : Space n := δ⁻¹ • z
  let c := f (δ • coreMap n x)
  let g : Space n → ℝ := fun w => f (δ • w)-c
  have hfd : ContDiff ℝ 3 (fun w : Space n => f (δ • w)) := hf.comp (contDiff_id.const_smul δ)
  have hg : ContDiff ℝ 3 g := hfd.sub contDiff_const
  have ho (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j g (coreMap n x)‖ ≤ M*δ := by
    by_cases hj0 : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero, g, c, sub_self, norm_zero]
      exact mul_nonneg hM hδ.le
    · rw [jet_sub_const hfd c _ j (by omega) (by omega)]
      have hs := linear_scale_jet_le hf δ (coreMap n x) j (by omega)
      rw [abs_of_pos hδ] at hs
      calc
        _ ≤ ‖iteratedFDeriv ℝ j f (δ • coreMap n x)‖*δ^j := hs
        _ ≤ (M*δ/δ^j)*δ^j := mul_le_mul_of_nonneg_right
          (houter j (by omega) (by omega) _) (pow_nonneg hδ.le _)
        _ = M*δ := by field_simp
  have hi (j : ℕ) (hj0 : 1 ≤ j) (hjk : j ≤ k) :
      ‖iteratedFDeriv ℝ j (coreMap n) x‖ ≤ K^j :=
    (hcore j hj0 (by omega) x).trans (by simpa only [pow_one] using pow_le_pow_right₀ hK hj0)
  have hcomp := norm_iteratedFDeriv_comp_le hg (coreMap_contDiff n)
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk) x ho hi
  have hs := linear_scale_jet_le (hg.comp (coreMap_contDiff n)) δ⁻¹ z k hk
  have he : (fun w : Space n => (g ∘ coreMap n) (δ⁻¹ • w)) =
      fun w => f (flattenMap n δ w)-c := by
    ext w
    rw [flattenMap_eq_scaled_coreMap n δ hδ.ne']
    rfl
  have hfc : ContDiff ℝ 3 (fun w => f (flattenMap n δ w)) := hf.comp (flattenMap_contDiff n δ)
  rw [he, jet_sub_const hfc c z k hk0 hk,
    abs_of_pos (inv_pos.mpr hδ)] at hs
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (g ∘ coreMap n) x‖*(δ⁻¹)^k := hs
    _ ≤ ((k.factorial:ℝ)*(M*δ)*K^k)*(δ⁻¹)^k :=
      mul_le_mul_of_nonneg_right hcomp (pow_nonneg (inv_nonneg.mpr hδ.le) _)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring

theorem flattened_gradient_coordinate_zero (n : ℕ) (a β δ : ℝ) (hδ : 0 < δ)
    (z : Space n) (j : Fin (n+1)) (hj : |z j| ≤ δ) :
    gradient (flattenedResidual n a β δ) z j = 0 := by
  have hd := ((R_contDiff n a β).differentiable (by norm_num) (flattenMap n δ z)).hasFDerivAt.comp z
    ((flattenMap_contDiff n δ).differentiable (by norm_num) z).hasFDerivAt
  change gradient (R n a β ∘ flattenMap n δ) z j = 0
  rw [gradient_coordinate_eq hd, ContinuousLinearMap.comp_apply,
    flattenMap_gradient_kills_small δ hδ z j hj, map_zero]

theorem flattened_gradient_support (n r : ℕ) (a β δ : ℝ) (hδ : 0 < δ)
    (z : Space n) (hz : ∀ j : Fin (n+1), r ≤ j.val → |z j| ≤ δ)
    (j : Fin (n+1)) (hj : r ≤ j.val) : gradient (flattenedResidual n a β δ) z j = 0 :=
  flattened_gradient_coordinate_zero n a β δ hδ z j (hz j hj)

theorem scale_budget_mono (B a β δ : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hβ : 0 < β) (hδ : 0 < δ) (hδβ : δ ≤ β) (j : ℕ) (hj : 1 ≤ j) :
    B*a/β^j ≤ (B*a/β)*δ/δ^j := by
  have hp : (δ/β)^j ≤ δ/β := pow_le_of_le_one (div_nonneg hδ.le hβ.le)
    ((div_le_one hβ).mpr hδβ) (by omega)
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hB ha)
  apply (le_div_iff₀ (pow_pos hδ j)).mpr
  convert hm using 1 <;> simp only [div_pow, div_eq_mul_inv] <;> ring

/-- One numerical constant controls all three positive derivative orders of
the actual flattened residual. The amplitude is still explicit. -/
theorem amplitude_derivative_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (a β δ : ℝ), 0 ≤ a → 0 < β → 0 < δ → δ ≤ β → ∀ z : Space n,
      |flattenedResidual n a β δ z| ≤ C*a ∧
      ∀ j : Fin 3, ‖iteratedFDeriv ℝ (j.val+1) (flattenedResidual n a β δ) z‖ ≤ C*a/(β*δ^j.val) := by
  obtain ⟨b,hb0,hb⟩ := R_uniform_jet_bound
  let B := 1+∑ j, b j
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hb0 j))
  have hbB (j : Fin 4) : b j ≤ B := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hb0 l) (Finset.mem_univ j)
    dsimp [B]
    linarith
  obtain ⟨K,hK,hcore⟩ := coreMap_common_jet_bound
  let d : Fin 3 → ℝ := fun j => ((j.val+1).factorial:ℝ)*B*K^(j.val+1)
  have hd (j : Fin 3) : 0 ≤ d j := by dsimp [d]; positivity
  let C := B+∑ j, d j
  have hC : 1 ≤ C := by
    have hs : 0 ≤ ∑ j, d j := Finset.sum_nonneg (fun j _ => hd j)
    dsimp [C]
    linarith
  have hBC : B ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hd j))
  have hdC (j : Fin 3) : d j ≤ C := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hd l) (Finset.mem_univ j)
    dsimp [C]
    linarith
  refine ⟨C,hC,fun n a β δ ha hβ hδ hδβ z => ⟨?_,fun j => ?_⟩⟩
  · have hzero := hb 0 n a β ha hβ (flattenMap n δ z)
    simp only [Fin.val_zero, norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, div_one] at hzero
    exact hzero.trans (mul_le_mul_of_nonneg_right ((hbB 0).trans hBC) ha)
  · have houter (l : ℕ) (hl0 : 1 ≤ l) (hl : l ≤ 3) (w : Space n) :
        ‖iteratedFDeriv ℝ l (R n a β) w‖ ≤ (B*a/β)*δ/δ^l := by
      have hh := hb ⟨l,by omega⟩ n a β ha hβ w
      exact hh.trans ((div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hbB ⟨l,by omega⟩) ha) (pow_nonneg hβ.le _)).trans
        (scale_budget_mono B a β δ (by linarith) ha hβ hδ hδβ l hl0))
    have hh := flatten_positive_jet_bound (R_contDiff n a β) K (B*a/β) δ hK (by positivity) hδ
      (hcore n) houter z (j.val+1) (by omega) (by omega)
    have he : ((j.val+1).factorial:ℝ)*(B*a/β)*K^(j.val+1)*δ/δ^(j.val+1) = d j*a/(β*δ^j.val) := by
      dsimp [d]
      rw [pow_succ]
      field_simp
      ring
    rw [he] at hh
    exact hh.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hdC j) ha) (by positivity))

/-- The exact derivative scales in the manuscript's flattening lemma. The
bound holds already for δ≤β; hence in particular for δ≤β/16. -/
theorem source_flattening_derivative_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (η L β δ : ℝ), 0 ≤ η → η ≤ 1 → 0 ≤ L → 0 < β → 0 < δ → δ ≤ β/16 →
      ∀ z : Space n, |flattenedResidual n (η*L*β^2) β δ z| ≤ C*L*β^2 ∧
      ∀ j : Fin 3, ‖iteratedFDeriv ℝ (j.val+1) (flattenedResidual n (η*L*β^2) β δ) z‖ ≤ C*L*β/δ^j.val := by
  obtain ⟨C,hC,hb⟩ := amplitude_derivative_bounds
  refine ⟨C,hC,fun n η L β δ hη hη1 hL hβ hδ hδβ z => ?_⟩
  have ha : 0 ≤ η*L*β^2 := by positivity
  have ha' : η*L*β^2 ≤ L*β^2 := by nlinarith [mul_le_mul_of_nonneg_right hη1 (mul_nonneg hL (sq_nonneg β))]
  have hh := hb n (η*L*β^2) β δ ha hβ hδ (by linarith) z
  constructor
  · exact hh.1.trans (by nlinarith [mul_le_mul_of_nonneg_left ha' (show 0 ≤ C by linarith)])
  · intro j
    apply (hh.2 j).trans
    calc
      _ ≤ C*(L*β^2)/(β*δ^j.val) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha' (by linarith)) (by positivity)
      _ = C*L*β/δ^j.val := by field_simp; ring

end Bilevel.ZeroChainFlatteningBounds
