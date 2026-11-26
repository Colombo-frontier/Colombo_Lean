import Bilevel.ChiOuterUpperTrace
import Bilevel.ChiOuterSourceUpperBase
import Bilevel.ChiOuterCarrierSignalLedger

/-! Direct placement of the complete depth-zero macro/micro objective in
the upper potential. The inactive potential is a fixed flattened scalar. -/
noncomputable section
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def core (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    Joint E (Blocks m F) → ℝ := jointOuter m M ν D ρ R 0 1

def signal (m : ℕ) (M : Node E) (D : Geometry F) : Joint E (Blocks m F) → ℝ :=
  outerFineSignal m M D 0 ((D 0 []).width/16)

def inactiveCore (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (z : Joint E (Blocks m F)) : ℝ := core m M ν D ρ R z-signal m M D z

theorem core_eq_upperBase (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    core m M ν D ρ R=upperBase m M ν D 0 (ρ 0) (R 0) := by
  funext z
  simpa only [core,Finset.univ_eq_empty,Finset.sum_empty,add_zero] using
    upperBase_trace m M ν D ρ R 0 z

theorem core_dilation (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (K : ℝ) (x : E) (v : Blocks m F) :
    core m M ν D ρ R (pack x (K • v))=jointOuter m M ν D ρ R 0 K (pack x v) := by
  change outerObjective M ν D ρ R 0 x (padded (1 • (K • v)))=
    outerObjective M ν D ρ R 0 x (padded (K • v))
  rw [one_smul]

theorem core_contDiff (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    ContDiff ℝ 3 (core m M ν D ρ R) := jointOuter_contDiff m M ν D ρ R 0 1 3

theorem signal_contDiff (m : ℕ) (M : Node E) (D : Geometry F) : ContDiff ℝ 3 (signal m M D) :=
  outerFineSignal_contDiff m M D 0 ((D 0 []).width/16)

theorem inactiveCore_contDiff (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    ContDiff ℝ 3 (inactiveCore m M ν D ρ R) :=
  (core_contDiff m M ν D ρ R).sub (signal_contDiff m M D)

theorem signal_eq_frontier_difference (m : ℕ) (M : Node E) (D : Geometry F) (z : Joint E (Blocks m F)) :
    signal m M D z=outerFineFrontier m M D 0 z-
      outerFineFlatFrontier m M D 0 ((D 0 []).width/16) z :=
  outerFineSignal_eq_sub m M D 0 ((D 0 []).width/16) z

theorem source_core_budgets (A Kminus ζ cn CR Km : ℝ) (hA : 0≤A) (hK : 1≤Kminus)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) :
    ∃ C : ℝ,1≤C ∧
      ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
        ∀ (r η weight : ℕ → ℝ),(∀ j,1≤r j) → r 0=1 → (∀ j,0<η j) → (∀ j,η j≤1) →
        (∀ j,128≤cn/(η j)^2) → (∀ j,0<weight j) → (∀ j,weight j≤1) →
        ∀ (U : Space n →ₗᵢ[ℝ] E)
          (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
        let M := sourceMacroNode n initial Km U
        let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
        let ρ := fun j => weight j*(D j []).nu
        let R := fun j => (D j []).radius
        ∀ (m : ℕ) (z : Joint E (Blocks m F)),
          ‖iteratedFDeriv ℝ 2 (core m M (initial.curvature/24) D ρ R) z‖≤C*initial.curvature ∧
          ‖gradient (fun u => core m M (initial.curvature/24) D ρ R (pack z.fst u)) z.snd‖≤C*initial.force ∧
          ‖gradient (signal m M D) z‖≤C*((D 0 []).ell*(D 0 []).width) := by
  obtain ⟨Cu,hCu,hupper⟩ := source_upper_base_budgets A Kminus ζ cn CR Km hA hK hζ hζ1 hcn hcn1 hCR hCRcn hKm
  obtain ⟨Cs,hCs,hsignal⟩ := source_outer_signal_ledger
  let C := Cu+Cs^2
  have hC : 1≤C := by dsimp [C]; nlinarith only [hCu,sq_nonneg Cs]
  have hCuC : Cu≤C := by dsimp [C]; linarith only [sq_nonneg Cs]
  have hCsC : Cs^2≤C := by dsimp [C]; linarith only [hCu]
  refine ⟨C,hC,fun E F _ _ _ _ _ _ n initial hl hw r η weight hr hr0 hη hη1 hlen hb hb1 U V => ?_⟩
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
  let ρ := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  have hp := parentScale_positive initial r η hl hw hr hη 1
  have hell : 0<(D 0 []).ell := hp.1
  have hβ : 0<(D 0 []).width := hp.2
  intro m z
  have hu := hupper E F n initial hl hw r η weight hr hr0 hη hη1 hlen hb hb1 U V 0 m z
  have hs := hsignal E F n initial hl hw r η weight A Kminus ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
    0 m ((D 0 []).width/16) (by positivity) le_rfl z 1 (by norm_num)
  rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq] at hs
  have hs' : ‖gradient (signal m M D) z‖≤Cs^2*((D 0 []).ell*(D 0 []).width) := by
    simpa only [Nat.zero_add,fineScale,pow_zero,div_one] using hs
  refine ⟨?_,?_,hs'.trans (mul_le_mul_of_nonneg_right hCsC (mul_pos hell hβ).le)⟩
  · rw [core_eq_upperBase]
    exact hu.1.trans (mul_le_mul_of_nonneg_right hCuC hl.le)
  · rw [core_eq_upperBase]
    exact hu.2.trans (mul_le_mul_of_nonneg_right hCuC (mul_pos hl hw).le)

end Bilevel.ChiUpperNoise
