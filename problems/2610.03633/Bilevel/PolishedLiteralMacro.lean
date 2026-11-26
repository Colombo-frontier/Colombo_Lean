import Bilevel.PolishedLiteralSize
import Bilevel.ChiBoundedChainLocalCertificate
import Bilevel.WrappedChainGap

/-! The exact exponential one-sided outer macroValue and its two-region endgame.
The radial coefficient is controlled by the proved global chain gradient
bound, with numerical radius and bowl parameters. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open ChiBoundedChain RadialWrapper ZeroChainPotential

theorem chain_frontier (n : ℕ) (ℓ h : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 < h)
    (z : Space n) (hlast : z (Fin.last n) < h) :
    ∃ j : Fin (n+1), z j < h ∧ gradient (chain n ℓ h) z j ≤ -(ℓ*h) := by
  classical
  let s : Finset (Fin (n+1)) := Finset.univ.filter (fun j => z j < h)
  have hs : s.Nonempty := ⟨Fin.last n, by simp [s, hlast]⟩
  let j := s.min' hs
  have hj : z j < h := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hn : (h⁻¹ • z) j < 1 := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact (inv_mul_lt_iff₀ hh).mpr (by simpa using hj)
  have hb := coordinate_endgame n (h⁻¹ • z) j hn (by
    intro i hi
    have hhzi : h ≤ z i := by
      by_contra he
      have himem : i ∈ s := by simp [s, lt_of_not_ge he]
      exact (not_lt_of_ge (Finset.min'_le s i himem)) hi
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact (le_inv_mul_iff₀ hh).mpr (by simpa using hhzi))
  refine ⟨j,hj,?_⟩
  rw [chain_gradient n ℓ h hh, PiLp.smul_apply, smul_eq_mul]
  simpa only [mul_neg, mul_one] using mul_le_mul_of_nonneg_left hb (mul_nonneg hℓ hh.le)

theorem interior_margin (n : ℕ) (ℓ h c q : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 < h)
    (hc : 0 ≤ c) (hq : 2/3 ≤ q) (hwidth : c*h ≤ (ℓ*h)/6)
    (z : Space n) (hz : z (Fin.last n) < h) :
    (ℓ*h)/2 ≤ ‖c • z + q • gradient (chain n ℓ h) z‖ := by
  obtain ⟨j,hj,hgrad⟩ := chain_frontier n ℓ h hℓ hh z hz
  apply negative_coordinate_norm_margin _ j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hrad := mul_le_mul_of_nonneg_left hj.le hc
  have hgrad0 := chain_gradient_nonpos n ℓ h hℓ hh z j
  have hqg := mul_le_mul_of_nonpos_right hq hgrad0
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def macroValue (n : ℕ) (ℓ h ν R : ℝ) (U : Space n →ₗᵢ[ℝ] E) : E → ℝ :=
  wrapped ν R (chain n ℓ h) U.toContinuousLinearMap.adjoint

theorem macro_hasGradientAt (n : ℕ) (ℓ h ν R : ℝ) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    HasGradientAt (macroValue n ℓ h ν R U)
      (wrappedGradient ν R u (U (gradient (chain n ℓ h)
        (WrappedChain.coordinates n R U u)))) u := by
  have hd := wrapped_hasGradientAt ν R hR (chain n ℓ h)
    U.toContinuousLinearMap.adjoint u _
    (((chain_contDiff n ℓ h 1).differentiable (by norm_num))
      (WrappedChain.coordinates n R U u)).hasGradientAt
  simpa only [macroValue, ContinuousLinearMap.adjoint_adjoint,
    LinearIsometry.coe_toContinuousLinearMap] using hd

theorem macro_endgame_from_bound (n : ℕ) (ℓ h ν R G : ℝ)
    (hℓ : 0 ≤ ℓ) (hh : 0 < h) (hν : 0 ≤ ν) (hR : 0 < R) (hG : 0 ≤ G)
    (hbound : ∀ z : Space n, ‖gradient (chain n ℓ h) z‖ ≤ G)
    (hbudget : 4*G ≤ ν*R) (hwidth : (5*ν/4)*h ≤ (ℓ*h)/6)
    (hexterior : (ℓ*h)/2 ≤ 2*ν*R/3-G)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hlast : WrappedChain.coordinates n R U u (Fin.last n) < h) :
    (ℓ*h)/2 ≤ ‖gradient (macroValue n ℓ h ν R U) u‖ := by
  let z := WrappedChain.coordinates n R U u
  let p := gradient (chain n ℓ h) z
  have hp : ‖p‖ ≤ G := hbound z
  rw [(macro_hasGradientAt n ℓ h ν R hR U u).gradient]
  change (ℓ*h)/2 ≤ ‖wrappedGradient ν R u (U p)‖
  rcases le_total ‖u‖ R with hu|hu
  · have hz : ‖z‖ ≤ R := (frame_adjoint_norm_le U _).trans (compress_norm_le_radius R hR u)
    have hi : ⟪z,p⟫ ≤ R*G := (real_inner_le_norm z p).trans
      (mul_le_mul hz hp (norm_nonneg _) hR.le)
    have hDbudget : 2*(R*G) ≤ ν*R^2 := by
      have hb := mul_le_mul_of_nonneg_right hbudget hR.le
      nlinarith
    obtain ⟨hcl,hcu⟩ := radialCoefficient_bounds_from_budgets ν R G (R*G)
      hR hG (mul_nonneg hR.le hG) U u p hp hi hDbudget hbudget
    have hc0 : 0 ≤ radialCoefficient ν R U u p := (by positivity : 0 ≤ ν/2).trans hcl
    have hcwidth : radialCoefficient ν R U u p*h ≤ (ℓ*h)/6 :=
      (mul_le_mul_of_nonneg_right hcu hh.le).trans hwidth
    have hg := interior_margin n ℓ h (radialCoefficient ν R U u p) (scale R u)
      hℓ hh hc0 (scale_interior_lower R hR u hu) hcwidth z hlast
    have he := projected_wrappedGradient ν R U u p
    change U.toContinuousLinearMap.adjoint (wrappedGradient ν R u (U p)) =
      radialCoefficient ν R U u p • z + scale R u • p at he
    change (ℓ*h)/2 ≤ ‖radialCoefficient ν R U u p • z + scale R u • p‖ at hg
    rw [← he] at hg
    exact hg.trans (frame_adjoint_norm_le U _)
  · exact exterior_endgame ν R G (ℓ*h) hν hR hG hexterior u (U p) hu (by simpa using hp)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem numerical_macro_endgame_with_radius : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (n : ℕ) (ℓ h : ℝ), 0 < ℓ → 0 < h →
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (U : Space n →ₗᵢ[ℝ] F) (u : F),
    let R := K*h*Real.sqrt ((n:ℝ)+1)
    WrappedChain.coordinates n R U u (Fin.last n) < h →
      (ℓ*h)/2 ≤ ‖gradient (macroValue n ℓ h (ℓ/24) R U) u‖ := by
  obtain ⟨C,hC,hb⟩ := chain_gradient_norm_uniform
  let K := 192*(C+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hK1 : 1≤K := by dsimp [K];linarith
  refine ⟨K,hK1,?_⟩
  intro n ℓ h hℓ hh F _ _ _ U u
  dsimp only
  intro hlast
  let s := Real.sqrt ((n:ℝ)+1)
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hR : 0 < K*h*s := mul_pos (mul_pos hK hh) hs0
  apply macro_endgame_from_bound n ℓ h (ℓ/24) (K*h*s) (C*(ℓ*h)*s)
    hℓ.le hh (by positivity) hR (by positivity) (hb n ℓ h hℓ.le hh) _ _ _ U u hlast
  · dsimp [K]
    nlinarith [mul_nonneg (mul_nonneg hℓ.le hh.le) hs0.le,
      mul_nonneg hC (mul_nonneg (mul_nonneg hℓ.le hh.le) hs0.le)]
  · nlinarith [mul_pos hℓ hh]
  · have hscale := mul_le_mul_of_nonneg_left hs (mul_nonneg hℓ.le hh.le)
    dsimp [K]
    nlinarith [mul_nonneg hC (mul_nonneg (mul_nonneg hℓ.le hh.le) hs0.le)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem numerical_macro_endgame : ∃ K : ℝ,0<K ∧
    ∀ (n : ℕ) (ℓ h : ℝ),0<ℓ → 0<h →
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (U : Space n →ₗᵢ[ℝ] F) (u : F),
    let R := K*h*Real.sqrt ((n:ℝ)+1)
    WrappedChain.coordinates n R U u (Fin.last n)<h →
      (ℓ*h)/2≤‖gradient (macroValue n ℓ h (ℓ/24) R U) u‖ := by
  obtain ⟨K,hK,hcert⟩ := numerical_macro_endgame_with_radius
  exact ⟨K,lt_of_lt_of_le zero_lt_one hK,hcert⟩

end Bilevel.PolishedLiteral
