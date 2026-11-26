import Bilevel.ChiBoundedChainCompositionBounds

/-! Order-sensitive composition at a flattening scale, retaining the sharp
delta^(1-k) dependence without a dimension-dependent estimate. -/
noncomputable section
namespace Bilevel.ChiFlattenComposition
open ChiBoundedChain
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem positive_jets (f : E → F) (g : F → G) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (M K δ : ℝ) (hM : 0≤M) (hK : 0≤K) (hδ : 0<δ) (hδ1 : δ≤1) (x : E)
    (hf1 : ‖iteratedFDeriv ℝ 1 f x‖≤K)
    (hf2 : ‖iteratedFDeriv ℝ 2 f x‖≤K/δ)
    (hf3 : ‖iteratedFDeriv ℝ 3 f x‖≤K/δ^2)
    (hg1 : ‖iteratedFDeriv ℝ 1 g (f x)‖≤M)
    (hg2 : ‖iteratedFDeriv ℝ 2 g (f x)‖≤M)
    (hg3 : ‖iteratedFDeriv ℝ 3 g (f x)‖≤M) :
    ‖iteratedFDeriv ℝ 1 (g ∘ f) x‖≤M*(K+1)^3 ∧
    ‖iteratedFDeriv ℝ 2 (g ∘ f) x‖≤M*(K+1)^3/δ ∧
    ‖iteratedFDeriv ℝ 3 (g ∘ f) x‖≤M*(K+1)^3/δ^2 := by
  have h1 := Composition.first_comp_bound x (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) _)
  have h2 := Composition.second_comp_bound
    (hf.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega)))
    (hg.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega))) x
  have h3 := Composition.third_comp_bound hf hg x
  have hb1 : ‖iteratedFDeriv ℝ 1 (g ∘ f) x‖≤M*K := h1.trans (by gcongr)
  have hb2 : ‖iteratedFDeriv ℝ 2 (g ∘ f) x‖≤M*K^2+M*K/δ := h2.trans (by
    calc
      _≤M*K^2+M*(K/δ) := by gcongr
      _=_ := by ring)
  have hb3 : ‖iteratedFDeriv ℝ 3 (g ∘ f) x‖≤M*K^3+3*M*K^2/δ+M*K/δ^2 := h3.trans (by
    calc
      _≤M*K^3+3*M*K*(K/δ)+M*(K/δ^2) := by gcongr
      _=_ := by ring)
  have hc1 : M*K≤M*(K+1)^3 := by nlinarith [mul_nonneg hM (sq_nonneg K),mul_nonneg hM (pow_nonneg hK 3)]
  have hc2 : M*K^2+M*K≤M*(K+1)^3 := by nlinarith [mul_nonneg hM (sq_nonneg K),mul_nonneg hM (pow_nonneg hK 3)]
  have hc3 : M*K^3+3*M*K^2+M*K≤M*(K+1)^3 := by nlinarith
  have hd2 : δ^2≤δ := by nlinarith
  have hd21 : δ^2≤1 := hd2.trans hδ1
  refine ⟨hb1.trans hc1,hb2.trans ?_,hb3.trans ?_⟩
  · calc
      _≤M*K^2/δ+M*K/δ := add_le_add_right ((le_div_iff₀ hδ).mpr
        (mul_le_of_le_one_right (by positivity : 0≤M*K^2) hδ1)) _
      _=(M*K^2+M*K)/δ := by ring
      _≤_ := div_le_div_of_nonneg_right hc2 hδ.le
  · calc
      _≤M*K^3/δ^2+3*M*K^2/δ^2+M*K/δ^2 := by
        apply add_le_add_right
        exact add_le_add ((le_div_iff₀ (sq_pos_of_pos hδ)).mpr
          (mul_le_of_le_one_right (by positivity : 0≤M*K^3) hd21))
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ) hd2)
      _=(M*K^3+3*M*K^2+M*K)/δ^2 := by ring
      _≤_ := div_le_div_of_nonneg_right hc3 (sq_nonneg δ)

end Bilevel.ChiFlattenComposition
