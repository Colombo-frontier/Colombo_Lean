import SecondOrder.CompletionThird
import SecondOrder.BlockDirections
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def DimensionJetBound (C D : ℝ) (f : E → ℝ) (x : E) : Prop :=
  ‖f x‖ ≤ 1 ∧ ‖iteratedFDeriv ℝ 1 f x‖ ≤ C/Real.sqrt D ∧
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ C/D ∧ ‖iteratedFDeriv ℝ 3 f x‖ ≤ C/D

theorem iteratedFDeriv_linear_contraction (f : F → ℝ) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (k : ℕ) (hf : ContDiff ℝ k f) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x le_rfl]
  have hh := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k f (L x)) (fun _ => L)
  apply hh.trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one (fun _ _ => norm_nonneg L) (fun _ _ => hL)

theorem DimensionJetBound.comp_linear {f : F → ℝ} {C D : ℝ} (hf : ContDiff ℝ 3 f)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (x : E) (hb : DimensionJetBound C D f (L x)) :
    DimensionJetBound C D (f ∘ L) x := by
  refine ⟨hb.1, ?_, ?_, ?_⟩
  · exact (iteratedFDeriv_linear_contraction f L hL 1 (hf.of_le (show (1:WithTop ℕ∞) ≤ 3 by decide)) x).trans hb.2.1
  · exact (iteratedFDeriv_linear_contraction f L hL 2 (hf.of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)) x).trans hb.2.2.1
  · exact (iteratedFDeriv_linear_contraction f L hL 3 hf x).trans hb.2.2.2

theorem blockProj_norm_le_one {J : Type*} [Fintype J] (j : J) :
    ‖blockProj (E := E) j‖ ≤ 1 := by
  apply (blockProj (E := E) j).opNorm_le_bound (by norm_num)
  intro x
  simpa only [blockProj_apply, one_mul] using PiLp.norm_apply_le (p := (2:ENNReal)) x j

private theorem jet_scale_facts {C D : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) :
    (C/Real.sqrt D)*(C/Real.sqrt D) = C^2/D ∧
    (C/Real.sqrt D)*(C/D) ≤ C^2/D ∧ C/D ≤ C^2/D := by
  have hC0 : 0 ≤ C := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hs : 1 ≤ Real.sqrt D := Real.one_le_sqrt.mpr hD
  refine ⟨?_, ?_, ?_⟩
  · rw [← sq, div_pow, Real.sq_sqrt hD0]
  · have hh := mul_le_mul_of_nonneg_right (div_le_self hC0 hs) (div_nonneg hC0 hD0)
    convert hh using 1 <;> ring
  · apply div_le_div_of_nonneg_right _ hD0
    nlinarith

theorem dimensionJet_product_second {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (x : E)
    (hfx : DimensionJetBound C D f x) (hgx : DimensionJetBound C D g x) :
    ‖iteratedFDeriv ℝ 2 (fun y => f y*g y) x‖ ≤ 8*C^2/D := by
  have hh := norm_iteratedFDeriv_mul_le (n := 2) hf hg x (show (2:WithTop ℕ∞) ≤ 3 by decide)
  norm_num [Finset.sum_range_succ, norm_iteratedFDeriv_zero] at hh
  change ‖iteratedFDeriv ℝ 2 (fun y => f y*g y) x‖ ≤
    ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at hh
  rw [norm_iteratedFDeriv_zero] at hh
  obtain ⟨hf0, hf1, hf2, hf3⟩ := hfx
  obtain ⟨hg0, hg1, hg2, hg3⟩ := hgx
  have hp : ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+
      2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 2 f x‖*‖g x‖ ≤
      1*(C/D)+2*(C/Real.sqrt D)*(C/Real.sqrt D)+(C/D)*1 := by
    gcongr
  have hs := jet_scale_facts hC hD
  have hnn : 0 ≤ C^2/D := div_nonneg (sq_nonneg _) (by linarith)
  have hq : 1*(C/D)+2*(C/Real.sqrt D)*(C/Real.sqrt D)+(C/D)*1 ≤ 8*C^2/D := by
    simp only [div_eq_mul_inv] at hs hnn ⊢
    nlinarith [hs.1, hs.2.2]
  exact hh.trans (hp.trans hq)

theorem dimensionJet_product_third {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (x : E)
    (hfx : DimensionJetBound C D f x) (hgx : DimensionJetBound C D g x) :
    ‖iteratedFDeriv ℝ 3 (fun y => f y*g y) x‖ ≤ 8*C^2/D := by
  have hh := norm_iteratedFDeriv_mul_le (n := 3) hf hg x (show (3:WithTop ℕ∞) ≤ 3 by decide)
  norm_num [Finset.sum_range_succ, norm_iteratedFDeriv_zero] at hh
  change ‖iteratedFDeriv ℝ 3 (fun y => f y*g y) x‖ ≤
    ‖f x‖*‖iteratedFDeriv ℝ 3 g x‖+3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
      3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 3 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at hh
  rw [norm_iteratedFDeriv_zero] at hh
  obtain ⟨hf0, hf1, hf2, hf3⟩ := hfx
  obtain ⟨hg0, hg1, hg2, hg3⟩ := hgx
  have hp : ‖f x‖*‖iteratedFDeriv ℝ 3 g x‖+
      3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
      3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 3 f x‖*‖g x‖ ≤
      C/D+3*(C/Real.sqrt D)*(C/D)+3*(C/D)*(C/Real.sqrt D)+C/D := by
    calc
      _ ≤ 1*(C/D)+3*(C/Real.sqrt D)*(C/D)+3*(C/D)*(C/Real.sqrt D)+(C/D)*1 := by gcongr
      _ = _ := by ring
  have hs := jet_scale_facts hC hD
  have hq : C/D+3*(C/Real.sqrt D)*(C/D)+3*(C/D)*(C/Real.sqrt D)+C/D ≤ 8*C^2/D := by
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith [hs.2.1, hs.2.2]
  exact hh.trans (hp.trans hq)

end
end SecondOrder
