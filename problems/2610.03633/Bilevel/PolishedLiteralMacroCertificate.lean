import Bilevel.PolishedLiteralMacro
import Bilevel.PolishedLiteralSize
import Bilevel.WrappedChainGap

/-! All three conclusions of the literal one-sided macro lemma, for the
original exponential chain rather than a capped activation substitute. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential RadialWrapper
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual macro function has a numerical chain-count value budget. -/
theorem macro_lower (n : ℕ) (ℓ h ν R : ℝ) (hℓ : 0≤ℓ) (_hν : 0≤ν)
    (U : Space n →ₗᵢ[ℝ] E) (x : E) :
    bowl ν R x-((n:ℝ)+1)*(Real.exp 1*gaussianBound)*(ℓ*h^2)≤macroValue n ℓ h ν R U x := by
  have hc := chain_lower n ℓ h hℓ (U.toContinuousLinearMap.adjoint (compress R x))
  change _≤chain n ℓ h (U.toContinuousLinearMap.adjoint (compress R x))+bowl ν R x
  linarith only [hc]

theorem macro_zero (n : ℕ) (ℓ h ν R : ℝ) (U : Space n →ₗᵢ[ℝ] E) :
    macroValue n ℓ h ν R U 0=-(ℓ*h^2)*phi 0 := by
  simp [macroValue,wrapped,compress,bowl,chain,ZeroChainResidualScaled.scaled,value_zero]

theorem macro_gap (n : ℕ) (ℓ h ν R : ℝ) (hℓ : 0≤ℓ) (hν : 0≤ν)
    (U : Space n →ₗᵢ[ℝ] E) :
    macroValue n ℓ h ν R U 0-sInf (Set.range (macroValue n ℓ h ν R U))≤
      ((n:ℝ)+1)*(Real.exp 1*gaussianBound)*(ℓ*h^2) := by
  let C := ((n:ℝ)+1)*(Real.exp 1*gaussianBound)*(ℓ*h^2)
  have hlow (x : E) : -C≤macroValue n ℓ h ν R U x := by
    have hh := macro_lower n ℓ h ν R hℓ hν U x
    have hb := bowl_nonnegative ν R hν x
    dsimp only [C]
    linarith only [hh,hb]
  have hi : -C≤sInf (Set.range (macroValue n ℓ h ν R U)) :=
    le_csInf (Set.range_nonempty _) (by rintro _ ⟨x,rfl⟩; exact hlow x)
  have hz : macroValue n ℓ h ν R U 0≤0 := by
    rw [macro_zero]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg hℓ (sq_nonneg h))) (phi_nonneg 0)
  change _≤C
  linarith only [hi,hz]

theorem macro_coercive [FiniteDimensional ℝ E] (n : ℕ) (ℓ h ν R : ℝ)
    (hℓ : 0≤ℓ) (hν : 0<ν) (hR : 0<R) (U : Space n →ₗᵢ[ℝ] E) :
    Tendsto (macroValue n ℓ h ν R U) (cocompact E) atTop := by
  let C := ((n:ℝ)+1)*(Real.exp 1*gaussianBound)*(ℓ*h^2)+ν*R^2
  have ha : 0<ν*R := mul_pos hν hR
  have hlow (x : E) : (ν*R)*‖x‖-C≤macroValue n ℓ h ν R U x := by
    have h1 := macro_lower n ℓ h ν R hℓ hν.le U x
    have h2 := bowl_linear_lower ν R hν.le hR x
    dsimp only [C]
    linarith only [h1,h2]
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_norm_cocompact_atTop (E:=E)).eventually_ge_atTop ((b+C)/(ν*R))
  filter_upwards [hn] with x hx
  have hh := (div_le_iff₀ ha).mp hx
  have hl := hlow x
  nlinarith only [hh,hl]

/-- Source `lem:macro-endgame`: numerical constants precede all dimensions,
scales and frames, and margin, coercivity and initial gap concern one Hm. -/
theorem literal_macro_certificate : ∃ K : ℝ,1≤K ∧
    ∀ (n : ℕ) (ℓ h : ℝ),0<ℓ → 0<h →
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (U : Space n →ₗᵢ[ℝ] F),
    let R := K*h*Real.sqrt ((n:ℝ)+1)
    (∀ x,WrappedChain.coordinates n R U x (Fin.last n)<h →
      (ℓ*h)/2≤‖gradient (macroValue n ℓ h (ℓ/24) R U) x‖) ∧
    Tendsto (macroValue n ℓ h (ℓ/24) R U) (cocompact F) atTop ∧
    macroValue n ℓ h (ℓ/24) R U 0-sInf (Set.range (macroValue n ℓ h (ℓ/24) R U))≤
      ((n:ℝ)+1)*(Real.exp 1*gaussianBound)*(ℓ*h^2) := by
  obtain ⟨K,hK,hm⟩ := numerical_macro_endgame_with_radius
  refine ⟨K,hK,?_⟩
  intro n ℓ h hℓ hh F _ _ _ _ U
  have hR : 0<K*h*Real.sqrt ((n:ℝ)+1) := by positivity
  exact ⟨hm n ℓ h hℓ hh F U,macro_coercive n ℓ h (ℓ/24) _ hℓ.le (by positivity) hR U,
    macro_gap n ℓ h (ℓ/24) _ hℓ.le (by positivity) U⟩

end Bilevel.PolishedLiteral
