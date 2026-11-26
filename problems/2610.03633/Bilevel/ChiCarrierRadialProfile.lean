import Bilevel.ChiBoundedChainWrappedJets

/-! Exact amplitude/width scaling and radial composition for a bounded
profile with three bounded jets. This is a calculus helper, not a carrier theorem. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain

theorem scaled_radial_profile_jet_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (B a h R : ℝ) (hB : 0≤B) (ha : 0≤a) (hh : 0<h) (hhR : h≤R)
    (hb : ∀ k,k≤3 → ∀ z,‖iteratedFDeriv ℝ k f z‖≤B)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k ((ZeroChainResidualScaled.scaled f a h) ∘ WrappedChain.coordinates n R U) u‖≤
      100000*B*a/h^k := by
  by_cases hk0 : k=0
  · subst k
    simp only [norm_iteratedFDeriv_zero,Function.comp_apply,ZeroChainResidualScaled.scaled,
      Real.norm_eq_abs,abs_mul,abs_of_nonneg ha,pow_zero,div_one]
    have hh' := hb 0 (by norm_num) (h⁻¹ • WrappedChain.coordinates n R U u)
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hh'
    have hs := mul_le_mul_of_nonneg_left hh' ha
    nlinarith only [hs,mul_nonneg hB ha]
  · have hk1 : 1≤k := by omega
    have hout : ∀ j,1≤j → j≤3 → ∀ z,
        ‖iteratedFDeriv ℝ j (ZeroChainResidualScaled.scaled f a h) z‖≤(B*a/h)*h/h^j := by
      intro j _ hj z
      have hs := ZeroChainResidualScaled.scaled_jet_bound hf a h B ha hh j hj (hb j hj) z
      convert hs using 1
      field_simp
    have hin : ∀ j,1≤j → j≤3 → ∀ x : E,
        ‖iteratedFDeriv ℝ j (WrappedChain.coordinates n R U) x‖≤24*h/h^j := by
      intro j hj0 hj x
      exact ZeroChainWrappedResidual.coordinates_positive_jet_bound n R h hh hhR U x j hj0 hj
    have hs := ZeroChainCarry.positive_composition_jet_bound
      (ZeroChainResidualScaled.scaled_contDiff hf a h)
      (ZeroChainWrappedResidual.coordinates_contDiff n R U) 24 (B*a/h) h (by norm_num) (by positivity) hh
      hout hin u k hk1 hk
    have hfct : (k.factorial:ℝ)*24^k≤100000 := by interval_cases k <;> norm_num
    have hscale := mul_le_mul_of_nonneg_right hfct (show 0≤B*a/h^k by positivity)
    apply hs.trans
    convert hscale using 1 <;> field_simp <;> ring

end Bilevel.ChiCarrier
