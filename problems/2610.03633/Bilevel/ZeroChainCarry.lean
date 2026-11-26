import Bilevel.ZeroChainSchedule
import Bilevel.ZeroChainFlatteningBounds

/-! Exact finite decompositions and bounded jet overlap survive the smooth
radial/frame coordinate map. The composition estimate preserves the physical
resolution scale, including the first derivative. -/

noncomputable section
namespace Bilevel.ZeroChainCarry

open ZeroChain ZeroChainMultiscale ZeroChainResidualJets ZeroChainFlatteningBounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def carriedPiece (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) (H : E → Space n)
    (j : ℕ) (x : E) : ℝ := a * piece n J δ j (H x)

theorem carriedPiece_contDiff (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H) (j : ℕ) : ContDiff ℝ 3 (carriedPiece n J δ a H j) :=
  contDiff_const.mul ((piece_contDiff n J δ j).comp hH)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_carriedPiece (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) (H : E → Space n) (x : E) :
    (∑ j ∈ Finset.range (J+1), carriedPiece n J δ a H j x) =
      a * ZeroChainResidual.residual n (H x) := by
  simp only [carriedPiece, ← Finset.mul_sum, sum_piece]

theorem carriedPiece_flat (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H) (j : ℕ) (x : E)
    (hj : ¬jetActive n J δ (H x) j) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (carriedPiece n J δ a H j) x = 0 := by
  have hb (l : ℕ) (hl : l ≤ k) : ‖iteratedFDeriv ℝ l (piece n J δ j) (H x)‖ = 0 := by
    have he : iteratedFDeriv ℝ l (piece n J δ j) (H x) = 0 := by
      by_contra hn
      exact hj ⟨⟨l,by omega⟩,hn⟩
    rw [he,norm_zero]
  have hc := flat_jet_comp hH (piece_contDiff n J δ j) x k hk hb
  change iteratedFDeriv ℝ k (fun w => a • (piece n J δ j ∘ H) w) x = 0
  rw [iteratedFDeriv_const_smul_apply' (((piece_contDiff n J δ j).comp hH).of_le
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)).contDiffAt, hc, smul_zero]

def carriedActive (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) (H : E → Space n) (x : E) : Finset ℕ := by
  classical
  exact (Finset.range (J+1)).filter (fun j => ∃ k : Fin 4,
    iteratedFDeriv ℝ k.val (carriedPiece n J δ a H j) x ≠ 0)

theorem carriedActive_subset (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H) (x : E) :
    carriedActive n J δ a H x ⊆ activePieces n J δ (H x) := by
  classical
  intro j hj
  obtain ⟨hj, k, hk⟩ := Finset.mem_filter.mp hj
  apply Finset.mem_filter.mpr
  refine ⟨hj, ?_⟩
  by_contra hn
  exact hk (carriedPiece_flat n J δ a hH j x hn k.val (by omega))

theorem at_most_three_carried_pieces (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H)
    (hpos : ∀ j, j < J → 0 < δ j) (hsmall : ∀ j, j < J → δ j ≤ 1/16)
    (hsep : ∀ i j, i < j → j < J → 2*δ j ≤ δ i) (x : E) :
    (carriedActive n J δ a H x).card ≤ 3 :=
  (Finset.card_le_card (carriedActive_subset n J δ a hH x)).trans
    (at_most_three_active_pieces n J δ hpos hsmall hsep (H x))

/-- Positive-order composition bound at physical resolution δ. Unlike a
bound including the zeroth jet, this does not lose a factor of 1/δ. -/
theorem jet_sub_constant {f : F → ℝ} (hf : ContDiff ℝ 3 f) (c : ℝ) (x : F)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (fun w => f w-c) x = iteratedFDeriv ℝ k f x := by
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' (hf.of_le hk').contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (show k ≠ 0 by omega), Pi.zero_apply, add_zero]

theorem positive_composition_jet_bound {f : F → ℝ} {H : E → F}
    (hf : ContDiff ℝ 3 f) (hH : ContDiff ℝ 3 H)
    (K M δ : ℝ) (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (houter : ∀ j, 1 ≤ j → j ≤ 3 → ∀ w,
      ‖iteratedFDeriv ℝ j f w‖ ≤ M*δ/δ^j)
    (hinner : ∀ j, 1 ≤ j → j ≤ 3 → ∀ w,
      ‖iteratedFDeriv ℝ j H w‖ ≤ K*δ/δ^j)
    (x : E) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (f ∘ H) x‖ ≤ (k.factorial:ℝ)*M*K^k*δ/δ^k := by
  let g : F → ℝ := fun w => f (δ • w)-f (H x)
  let h : E → F := fun w => δ⁻¹ • H w
  have hfd : ContDiff ℝ 3 (fun w : F => f (δ • w)) := hf.comp (contDiff_id.const_smul δ)
  have hg : ContDiff ℝ 3 g := hfd.sub contDiff_const
  have hh : ContDiff ℝ 3 h := hH.const_smul δ⁻¹
  have hout (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j g (h x)‖ ≤ M*δ := by
    by_cases hj0 : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero, g, h, smul_smul, mul_inv_cancel₀ hδ.ne',
        one_smul, sub_self, norm_zero]
      exact mul_nonneg hM hδ.le
    · change ‖iteratedFDeriv ℝ j (fun w => f (δ • w)-f (H x)) (h x)‖ ≤ _
      rw [jet_sub_constant hfd (f (H x)) _ j (by omega) (by omega)]
      let A : F →L[ℝ] F := δ • ContinuousLinearMap.id ℝ F
      have hA : ‖A‖ ≤ δ := by
        apply ContinuousLinearMap.opNorm_le_bound _ hδ.le
        intro v
        change ‖δ • v‖ ≤ δ*‖v‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      have hc := A.iteratedFDeriv_comp_right hf (h x)
        (show (j:WithTop ℕ∞) ≤ 3 by exact_mod_cast (show j ≤ 3 by omega))
      change ‖iteratedFDeriv ℝ j (f ∘ A) (h x)‖ ≤ M*δ
      rw [hc]
      have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ j f (A (h x))) (fun _ => A)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
      calc
        _ ≤ ‖iteratedFDeriv ℝ j f (A (h x))‖ * ‖A‖^j := hb
        _ ≤ (M*δ/δ^j)*δ^j := mul_le_mul (houter j (by omega) (by omega) _)
          (pow_le_pow_left₀ (norm_nonneg A) hA j) (pow_nonneg (norm_nonneg A) _) (by positivity)
        _ = M*δ := by field_simp
  have hin (j : ℕ) (hj0 : 1 ≤ j) (hjk : j ≤ k) : ‖iteratedFDeriv ℝ j h x‖ ≤ (K/δ)^j := by
    change ‖iteratedFDeriv ℝ j (fun w => δ⁻¹ • H w) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hH.of_le
      (show (j:WithTop ℕ∞) ≤ 3 by exact_mod_cast (show j ≤ 3 by omega))).contDiffAt]
    have hsm : ‖δ⁻¹ • iteratedFDeriv ℝ j H x‖ ≤ δ⁻¹ * ‖iteratedFDeriv ℝ j H x‖ := by
      apply ContinuousMultilinearMap.opNorm_le_bound
      · positivity
      intro v
      simp only [ContinuousMultilinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hδ)]
      exact (mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ j H x).le_opNorm v) (by positivity)).trans_eq (by ring)
    have hpow : K ≤ K^j := by simpa only [pow_one] using pow_le_pow_right₀ hK hj0
    calc
      _ ≤ δ⁻¹ * ‖iteratedFDeriv ℝ j H x‖ := hsm
      _ ≤ δ⁻¹*(K*δ/δ^j) := mul_le_mul_of_nonneg_left (hinner j hj0 (by omega) x) (by positivity)
      _ = K/δ^j := by field_simp
      _ ≤ K^j/δ^j := div_le_div_of_nonneg_right hpow (pow_nonneg hδ.le _)
      _ = (K/δ)^j := (div_pow K δ j).symm
  have hc := norm_iteratedFDeriv_comp_le hg hh
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk) x hout hin
  have he : g ∘ h = fun w => (f ∘ H) w-f (H x) := by
    ext w
    simp only [Function.comp_apply, g, h, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
  rw [he, jet_sub_constant (hf.comp hH) (f (H x)) x k hk0 hk] at hc
  convert hc using 1
  rw [div_pow]
  ring

end Bilevel.ZeroChainCarry
