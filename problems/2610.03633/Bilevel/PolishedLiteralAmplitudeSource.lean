import Bilevel.PolishedLiteralAmplitudeBudgets
import Bilevel.PolishedLiteralLowerGeometry

/-! The independent-chain source of fb:eq:K is an exact isometric
restriction of the stronger selected family, using one selector equal to
one at the frozen macro origin. This recovers the manuscript's actual
(u,s) variables and the uncapped exponential residual without extra
geometric or derivative assumptions. -/
noncomputable section
set_option maxHeartbeats 500000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ChiRecursive ZeroChainSchedule
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def singleParameters (n : ℕ) (μ ell β R v : ℝ) (V : Space n →ₗᵢ[ℝ] U) (hβ : 0<β) (hv : 1≤v) :
    Parameters (X:=Space 0) (U:=U) where
  macroNode := {
    n := 0
    ell := ell
    width := β
    receiver := 0
    nu := 0
    force := 0
    parentWidth := β
    tailRadius := β
    radius := β
    frame := LinearIsometry.id }
  macroRadial:=0
  n:=n
  μ:=μ
  L:=ell
  β:=β
  radius:=R
  ν:=0
  receiver:=0
  force:=0
  frames:=fun _ => V
  J:=levels v
  δ:=resolution (1/64) β v
  w:=width (1/64) β v
  w_pos:=fun j _ => width_pos (1/64) β v (by norm_num) hβ hv j

theorem selector_single_origin : selector 0 (0 : Fin 1) (0 : Space 0)=1 := by
  change energyCutoff (∑ j : Fin 1,if (0 : Fin 1)≤j then coordinateCutoff ((0 : Space 0) j)^2 else 0)=1
  simp only [Fin.sum_univ_one,le_refl,if_true,PiLp.zero_apply]
  rw [coordinateCutoff_zero (by norm_num : |(0:ℝ)|≤1/4)]
  norm_num
  exact energyCutoff_one (by norm_num)

theorem singleParameters_residual (n : ℕ) (μ ell β R v : ℝ) (V : Space n →ₗᵢ[ℝ] U) (hβ : 0<β) (hv : 1≤v)
    (u : U) :
    (singleParameters n μ ell β R v V hβ hv).selectedResidual (PrimitiveGeometry.pack 0 u)=
      residual n ell β (WrappedChain.coordinates n R V u) := by
  change (∑ i : Fin 1,wrappedSelector (singleParameters n μ ell β R v V hβ hv).macroNode i 0*
    residual n ell β (WrappedChain.coordinates n R V u))=_
  rw [Fin.sum_univ_one]
  have hψ : wrappedSelector (singleParameters n μ ell β R v V hβ hv).macroNode (0 : Fin 1) 0=1 := by
    unfold wrappedSelector
    rw [Node.coordinates_zero,smul_zero]
    exact selector_single_origin
  rw [hψ,one_mul]

theorem singleParameters_piece (n : ℕ) (μ ell β R v : ℝ) (V : Space n →ₗᵢ[ℝ] U) (hβ : 0<β) (hv : 1≤v)
    (j : ℕ) (u : U) :
    (singleParameters n μ ell β R v V hβ hv).selectedPiece j (PrimitiveGeometry.pack 0 u)=
      piece n (levels v) ell β (resolution (1/64) β v) j (WrappedChain.coordinates n R V u) := by
  change (∑ i : Fin 1,wrappedSelector (singleParameters n μ ell β R v V hβ hv).macroNode i 0*
    piece n (levels v) ell β (resolution (1/64) β v) j (WrappedChain.coordinates n R V u))=_
  rw [Fin.sum_univ_one]
  have hψ : wrappedSelector (singleParameters n μ ell β R v V hβ hv).macroNode (0 : Fin 1) 0=1 := by
    unfold wrappedSelector
    rw [Node.coordinates_zero,smul_zero]
    exact selector_single_origin
  rw [hψ,one_mul]

def singleAmplitudeLift (n : ℕ) (μ ell Lden β R v : ℝ) (V : Space n →ₗᵢ[ℝ] U)
    (q : Joint U ℝ) : ℝ :=
  μ/(2*Lden^2)*(residual n ell β (WrappedChain.coordinates n R V q.fst))^2-
    μ/Lden*(∑ j ∈ Finset.range (levels v+1),
      piece n (levels v) ell β (resolution (1/64) β v) j (WrappedChain.coordinates n R V q.fst)*
        PolishedLiteralCompensated.normal (width (1/64) β v j) q.snd)

def singleZeroOuterLM : Joint U ℝ →ₗ[ℝ] FullMeanSpace (X:=Space 0) (U:=U) where
  toFun q:=PrimitiveGeometry.pack 0 q
  map_add' a b:=by
    change PrimitiveGeometry.pack (0 : Joint (Space 0) U) (a+b)=PrimitiveGeometry.pack ((0 : Joint (Space 0) U)+0) (a+b)
    rw [add_zero]
  map_smul' c q:=by
    change PrimitiveGeometry.pack (0 : Joint (Space 0) U) (c • q)=PrimitiveGeometry.pack (c • (0 : Joint (Space 0) U)) (c • q)
    rw [smul_zero]

omit [CompleteSpace U] in
theorem singleZeroOuterLM_norm (q : Joint U ℝ) : ‖singleZeroOuterLM q‖≤‖q‖ := by
  have h := norm_sq (singleZeroOuterLM q)
  change ‖singleZeroOuterLM q‖^2=‖(0 : Joint (Space 0) U)‖^2+‖q‖^2 at h
  simp only [norm_zero,zero_pow (by norm_num : 2≠0),zero_add] at h
  nlinarith [norm_nonneg q,norm_nonneg (singleZeroOuterLM q)]

def singleZeroOuter : Joint U ℝ →L[ℝ] FullMeanSpace (X:=Space 0) (U:=U) :=
  singleZeroOuterLM.mkContinuous 1 (fun q => by simpa only [one_mul] using singleZeroOuterLM_norm q)

omit [CompleteSpace U] in
theorem singleZeroOuter_norm : ‖singleZeroOuter (U:=U)‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun q => by simpa only [one_mul] using singleZeroOuterLM_norm q)

def singleLiftEmbed : Joint U ℝ →L[ℝ] PolishedLiteralCompensated.LowerSpace (Joint (Space 0) U) :=
  fullLowerEmbed.comp singleZeroOuter

omit [CompleteSpace U] in
theorem singleLiftEmbed_norm : ‖singleLiftEmbed (U:=U)‖≤1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [fullLowerEmbed_norm (X:=Space 0) (U:=U),singleZeroOuter_norm (U:=U),
      norm_nonneg (fullLowerEmbed (X:=Space 0) (U:=U)),norm_nonneg (singleZeroOuter (U:=U))])

theorem singleAmplitudeLift_eq_restriction (n : ℕ) (μ ell Lden β R v : ℝ) (V : Space n →ₗᵢ[ℝ] U)
    (hβ : 0<β) (hv : 1≤v) :
    singleAmplitudeLift n μ ell Lden β R v V=
      (singleParameters n μ ell β R v V hβ hv).amplitudePerturbation Lden ∘ singleLiftEmbed := by
  funext q
  have he : singleLiftEmbed q=PolishedLiteralCompensated.pack _ (PrimitiveGeometry.pack 0 q.fst) q.snd 0 := rfl
  simp only [Function.comp_apply,Parameters.amplitudePerturbation_formula,he,
    PolishedLiteralCompensated.uProj_pack,PolishedLiteralCompensated.sProj_pack,
    singleParameters_residual,singleParameters_piece]
  rfl

/-- Exact source fb:lem:multiscale, including its unrestricted amplitude
schedule v=theta/alpha and actual normal linearity at r/Lden. -/
theorem literal_source_amplitude_multiscale : ∃ C τ : ℝ,1≤C ∧ 0<τ ∧
    ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (n : ℕ) (μ ell Lden β R α θ : ℝ) (V : Space n →ₗᵢ[ℝ] U),
      0<μ → 0<Lden → 0<α → α≤1 → 1≤θ → ell=α*Lden → 0<β → β≤R →
      (∀ q : Joint U ℝ,
        ‖iteratedFDeriv ℝ 2 (singleAmplitudeLift n μ ell Lden β R (θ/α) V) q‖≤C*μ*(β*Real.sqrt (α*θ)+α^2*β^2) ∧
        ‖iteratedFDeriv ℝ 3 (singleAmplitudeLift n μ ell Lden β R (θ/α) V) q‖≤C*μ*(θ+α^2*β)) ∧
      (β*θ≤τ → ∀ u j,j≤levels (θ/α) →
        |residual n ell β (WrappedChain.coordinates n R V u)/Lden|≤width (1/64) β (θ/α) j/4 ∧
        PolishedLiteralCompensated.normal (width (1/64) β (θ/α) j)
          (residual n ell β (WrappedChain.coordinates n R V u)/Lden)=
            residual n ell β (WrappedChain.coordinates n R V u)/Lden ∧
        deriv (PolishedLiteralCompensated.normal (width (1/64) β (θ/α) j))
          (residual n ell β (WrappedChain.coordinates n R V u)/Lden)=1) := by
  obtain ⟨C,τ,hC,hτ,hbud⟩ := actual_literal_amplitude_budgets
  refine ⟨C,τ,hC,hτ,?_⟩
  intro U _ _ _ n μ ell Lden β R α θ V hμ hLd hα hα1 hθ hell hβ hR
  have hv : 1≤θ/α := (le_div_iff₀ hα).mpr (by linarith)
  let P := singleParameters n μ ell β R (θ/α) V hβ hv
  have hh := hbud (Space 0) U P Lden α θ hLd hα hα1 hθ hell hμ hβ hR (le_refl _) (le_refl _) rfl rfl rfl
  constructor
  · intro q
    have hb := hh.1 (singleLiftEmbed q)
    have hres : singleAmplitudeLift n μ ell Lden β R (θ/α) V=P.amplitudePerturbation Lden ∘ singleLiftEmbed :=
      singleAmplitudeLift_eq_restriction n μ ell Lden β R (θ/α) V hβ hv
    rw [hres]
    have hcont := P.amplitudePerturbation_contDiff Lden
    constructor
    · apply (ChiOuter.contraction_jet_bound (singleLiftEmbed (U:=U)) (singleLiftEmbed_norm (U:=U)) hcont q 2 (by norm_num)).trans
      exact hb.1
    · apply (ChiOuter.contraction_jet_bound (singleLiftEmbed (U:=U)) (singleLiftEmbed_norm (U:=U)) hcont q 3 (by norm_num)).trans
      exact hb.2
  · intro hs u j hj
    have hc := hh.2 hs (PrimitiveGeometry.pack 0 u) j hj
    rw [singleParameters_residual] at hc
    have hwpos := width_pos (1/64) β (θ/α) (by norm_num) hβ hv j
    exact ⟨hc,PolishedLiteralCompensated.normal_core _ _ hwpos hc,
      PolishedLiteralCompensated.normal_deriv_core _ _ hwpos hc⟩

end Bilevel.PolishedLiteral
