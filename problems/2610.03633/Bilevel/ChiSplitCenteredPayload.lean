import Bilevel.ChiSplitCenteredSupport

/-! The actual scaled split payload minus its centered frontier has old
prefix support at both endpoints, including both terminal receivers. -/
noncomputable section
open scoped Topology RealInnerProductSpace
namespace Bilevel.ChiSplitChain
open ChiBoundedChain PrimitiveGeometry

theorem scalar_rescale_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : Differentiable ℝ f) (a h : ℝ) (z : E) :
    gradient (fun w => a*f (h⁻¹ • w)) z=(a/h) • gradient f (h⁻¹ • z) := by
  have hd := ((hf (h⁻¹ • z)).hasGradientAt.hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul h⁻¹)).const_mul a
  have hg : HasGradientAt (fun w => a*f (h⁻¹ • w)) ((a/h) • gradient f (h⁻¹ • z)) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd using 1
    ext v
    simp [InnerProductSpace.toDual_apply,div_eq_mul_inv]
    ring
  exact hg.gradient

def centeredPayload (n : ℕ) (ell h A ν g hp T : ℝ) : Latent n → ℝ :=
  fun z => payload n ell h A ν g hp T z-ChiSplitFine.frontier n ell h z

theorem centeredPayload_contDiff (n : ℕ) (ell h A ν g hp T : ℝ) :
    ContDiff ℝ 3 (centeredPayload n ell h A ν g hp T) :=
  (payload_contDiff n 3 ell h A ν g hp T).sub (ChiSplitFine.frontier_contDiff n ell h)

theorem centeredPayload_eventually_scaled_carrier (n : ℕ) (ell h A ν g hp T : ℝ) (hh : 0<h)
    (z : Latent n) (hz : |z.snd (Fin.last n)|<h/4) :
    centeredPayload n ell h A ν g hp T =ᶠ[𝓝 z] fun w => ell*h^2*carrier n (h⁻¹ • w) := by
  have ho : IsOpen {w : Latent n | |w.snd (Fin.last n)|<h/4} :=
    isOpen_lt (targetProjection (Fin.last n)).continuous.abs continuous_const
  filter_upwards [ho.mem_nhds hz] with w hw
  have ht := receiver_values_flat A ν g h hp T _ hh hw.le
  dsimp only [centeredPayload,payload,chain,ChiSplitFine.frontier,carrier]
  rw [ht.1,ht.2]
  ring

theorem centeredPayload_gradient_support (n r : ℕ) (ell h A ν g hp T : ℝ) (hh : 0<h)
    (z : Latent n) (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|<h/4) :
    (∀ k : Fin (n+1),r≤k.val → (gradient (centeredPayload n ell h A ν g hp T) z).fst k=0) ∧
    (∀ k : Fin (n+1),r≤k.val → (gradient (centeredPayload n ell h A ν g hp T) z).snd k=0) := by
  by_cases hr : r≤n
  · have ht := hz (Fin.last n) (by simpa using hr)
    have he := centeredPayload_eventually_scaled_carrier n ell h A ν g hp T hh z ht
    have hc : Differentiable ℝ (carrier n) := ((value_contDiff n 3).sub (frontier_contDiff n 3)).differentiable (by norm_num)
    have hs := carrier_gradient_support n r (h⁻¹ • z) (fun k hk =>
      ZeroChainResidualScaled.scaled_coordinate_small h hh z.snd k (hz k hk).le)
    rw [he.gradient_eq,scalar_rescale_gradient hc]
    constructor
    · intro k hk
      change (ell*h^2/h)*(gradient (carrier n) (h⁻¹ • z)).fst k=0
      rw [hs.1 k hk,mul_zero]
    · intro k hk
      change (ell*h^2/h)*(gradient (carrier n) (h⁻¹ • z)).snd k=0
      rw [hs.2 k hk,mul_zero]
  · constructor <;> intro k hk <;> have := k.isLt <;> omega

end Bilevel.ChiSplitChain
