import Bilevel.ChiSplitFineBounds

/-! Physical curvature/width scaling of the actual revised frontier and
flattening. These are the source's ell*beta*delta and ell*beta/delta^(j-1)
bounds with constants independent of chain length and all scale parameters. -/
noncomputable section
namespace Bilevel.ChiSplitFine
open ChiBoundedChain ZeroChainResidualScaled

def frontier (n : ℕ) (ℓ β : ℝ) : Latent n → ℝ := fun z => ℓ*β^2*ChiSplitChain.frontier n (β⁻¹ • z)
def flatFrontier (n : ℕ) (ℓ β δ : ℝ) : Latent n → ℝ := fun z => ℓ*β^2*flattened n (δ/β) (β⁻¹ • z)

theorem frontier_contDiff (n : ℕ) (ℓ β : ℝ) : ContDiff ℝ 3 (frontier n ℓ β) :=
  contDiff_const.mul ((ChiSplitChain.frontier_contDiff n 3).comp (contDiff_id.const_smul β⁻¹))

theorem flatFrontier_contDiff (n : ℕ) (ℓ β δ : ℝ) : ContDiff ℝ 3 (flatFrontier n ℓ β δ) :=
  contDiff_const.mul ((flattened_contDiff n (δ/β)).comp (contDiff_id.const_smul β⁻¹))

theorem source_flattening_error (n : ℕ) (ℓ β δ : ℝ) (hℓ : 0≤ℓ) (hβ : 0<β) (hδ : 0<δ)
    (z : Latent n) : |frontier n ℓ β z-flatFrontier n ℓ β δ z|≤
      (2*Real.sqrt (Real.exp 1))*ℓ*β*δ := by
  change |ℓ*β^2*ChiSplitChain.frontier n (β⁻¹ • z)-ℓ*β^2*flattened n (δ/β) (β⁻¹ • z)|≤_
  rw [← mul_sub,abs_mul,abs_of_nonneg (mul_nonneg hℓ (sq_nonneg β))]
  have hh := mul_le_mul_of_nonneg_left (flattening_error (div_pos hδ hβ) n (β⁻¹ • z))
    (mul_nonneg hℓ (sq_nonneg β))
  exact hh.trans_eq (by field_simp;ring)

theorem source_flattening_derivative_bounds : ∃ C : ℝ,1≤C ∧
    ∀ (n : ℕ) (ℓ β δ : ℝ),0≤ℓ → 0<β → 0<δ → δ≤β/16 →
      ∀ (j : Fin 3) (z : Latent n),
        ‖iteratedFDeriv ℝ (j.val+1) (flatFrontier n ℓ β δ) z‖≤C*ℓ*β/δ^j.val := by
  obtain ⟨C,hC,hb⟩ := flattened_positive_jet_bounds
  refine ⟨C,hC,fun n ℓ β δ hℓ hβ hδ hs j z => ?_⟩
  have hδβ : δ/β≤1/16 := (div_le_iff₀ hβ).mpr (by linarith)
  have hh  := ChiSplitChain.scaled_jet_bound (flattened_contDiff n (δ/β)) (ℓ*β^2) β (C/(δ/β)^j.val)
    (by positivity) hβ (j.val+1) (by omega) (hb n (δ/β) (div_pos hδ hβ) hδβ j) z
  apply hh.trans_eq
  rw [div_pow,pow_succ]
  field_simp
  ring

theorem source_frontier_jet_bounds : ∃ C : ℝ,1≤C ∧
    ∀ (n k : ℕ) (ℓ β : ℝ),k≤3 → 0≤ℓ → 0<β → ∀ z : Latent n,
      ‖iteratedFDeriv ℝ k (frontier n ℓ β) z‖≤C*ℓ*β^2/β^k := by
  obtain ⟨C,hC,hb⟩ := centered_uniform_jet_bound
  refine ⟨C,hC,fun n k ℓ β hk hℓ hβ z => ?_⟩
  have hh  := ChiSplitChain.scaled_jet_bound (ChiSplitChain.frontier_contDiff n 3) (ℓ*β^2) β C
    (by positivity) hβ k hk (hb n k hk) z
  exact hh.trans_eq (by ring)

end Bilevel.ChiSplitFine
