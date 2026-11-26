import Bilevel.EndpointTransportSourceOuterCoarse
import Bilevel.EndpointTransportNormalExtension
import Bilevel.ChiNormalizedExtensionJets

/-! Actual complete physical coarse normal sum, with source ledger bounds
summed only after every term is embedded in the same heterogeneous space. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiExtensionCalibration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def sourcePhysicalCoarseExtension {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (J s : ℕ)
    (index : Fin J → Fin s) (d : ℝ) (z : Full (PhysicalBase E J n D) s) : ℝ :=
  coarseSum index (physicalHierarchyCoarse Q M G P J) (fun i => coarseWidth G (i.val+1)) z/d

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem source_physical_coarse_sum_jets (Ar K ζ cn : ℝ) (hAr : 0≤Ar) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n D nM : ℕ) (Q : Rotations n D) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space nM →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block D),
      let M := sourceMacroNode nM initial Km U
      let G := sourceGeometry initial r η b Ar K ζ cn CR V
      ∀ (J s : ℕ) (P : ChiFine.Parameters),P.ℓ=(G J []).ell → P.β=(G J []).width →
      ∀ (index : Fin J → Fin s) (d : ℝ),0<d → ∀ z : Full (PhysicalBase E J n D) s,
      let N := fun i : Fin J => ((G (i.val+1) []).n:ℝ)+1
      let ell := fun i : Fin J => (G (i.val+1) []).ell
      let h := fun i : Fin J => (G (i.val+1) []).width
      ‖iteratedFDeriv ℝ 1 (sourcePhysicalCoarseExtension Q M G P J s index d) z‖≤
        ∑ i : Fin J,2*SmallGapLiftSupport.C*C^(J+2)*N i*ell i*(h i)^2/d ∧
      ‖iteratedFDeriv ℝ 2 (sourcePhysicalCoarseExtension Q M G P J s index d) z‖≤
        ∑ i : Fin J,4*SmallGapLiftSupport.C*C^(J+2)*ell i*h i*((N i)^(1/3:ℝ))^2/d ∧
      ‖iteratedFDeriv ℝ 3 (sourcePhysicalCoarseExtension Q M G P J s index d) z‖≤
        ∑ i : Fin J,8*SmallGapLiftSupport.C*C^(J+2)*ell i*(N i)^(1/3:ℝ)/d := by
  obtain ⟨C,hC,hledger⟩ := source_outer_physical_coarse_ledger Ar K ζ cn hAr hK hζ hζ1 hcn hcn1
  refine ⟨C,hC,?_⟩
  intro E _ _ _ n D nM Q initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  dsimp only
  let M := sourceMacroNode nM initial Km U
  let G := sourceGeometry initial r η b Ar K ζ cn CR V
  intro J s P hℓ hβ index d hd z
  let N := fun i : Fin J => ((G (i.val+1) []).n:ℝ)+1
  let ell := fun i : Fin J => (G (i.val+1) []).ell
  let h := fun i : Fin J => (G (i.val+1) []).width
  have hp (i : Fin J) := parentScale_positive initial r η hl hw hr hη (i.val+2)
  have hled (i : Fin J) (y : PhysicalBase E J n D) (k : ℕ) (hk : k≤3) :
      ‖iteratedFDeriv ℝ k (physicalHierarchyCoarse Q M G P J i) y‖≤
        C^(J+2)*ledgerScale (N i) (ell i) (h i) k := by
    have ht : i.val+1≤J := by omega
    have hraw := hledger E (PhysicalBase E J n D) n D nM Q initial hl hw r η b CR Km
      hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V J
      (baseMacroProjection J n D) (baseOrdinaryProjection J n D) (basePhysicalProjection J n D)
      (baseMacroProjection_norm_le J n D) (baseOrdinaryProjection_norm_le J n D)
      (basePhysicalProjection_norm_le J n D) J P hℓ hβ (i.val+1) ht y k hk
    exact hraw.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by omega))
      (ledgerScale_nonneg (by positivity) (hp i).1.le (hp i).2.le k))
  apply coarseSum_normalized_jets index (physicalHierarchyCoarse Q M G P J) N ell h (C^(J+2)) d
    (outerPhysicalCoarseFamily_contDiff J Q M (baseMacroProjection J n D) G
      (baseOrdinaryProjection J n D) (basePhysicalProjection J n D) P J)
    (fun i => by dsimp [N];have hn := Nat.cast_nonneg (α:=ℝ) (G (i.val+1) []).n;linarith)
    (fun i => (hp i).1.le) (fun i => (hp i).2) (pow_nonneg (by linarith) _) hd
  intro i y
  have h0 := hled i y 0 (by norm_num)
  have h1 := hled i y 1 (by norm_num)
  have h2 := hled i y 2 (by norm_num)
  have h3 := hled i y 3 (by norm_num)
  refine ⟨?_,?_,h2,?_⟩
  · simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,ledgerScale,mul_assoc] using h0
  · simpa only [ledgerScale,mul_assoc] using h1
  · simpa only [ledgerScale,mul_div_assoc] using h3

end Bilevel.EndpointTransportResponse
