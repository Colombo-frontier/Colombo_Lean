import Bilevel.ChiSourceCoarseFamily
import Bilevel.ChiNormalizedExtensionJets

/-! The actual source coarse extension, with all intermediate carriers and
the deepest revealed carrier, on a common space of dual normal variables. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def coarseWidths (D : Geometry F) (J : ℕ) (i : Fin J) : ℝ :=
  (D (i.val+1) []).width*((((D (i.val+1) []).n:ℝ)+1)^(1/3:ℝ))

def sourceCoarseExtension (m normals : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (index : Fin J → Fin normals) (d : ℝ) (z : Full (Joint E (Blocks m F)) normals) : ℝ :=
  coarseSum index (coarseFamily m M D J) (coarseWidths D J) z/d

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem source_coarse_extension_jets (A K ζ cn : ℝ) (hA : 0 ≤ A) (hK : 1 ≤ K)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hcn : 0 < cn) (hcn1 : cn ≤ 1) :
    ∃ C : ℝ,1 ≤ C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR Km : ℝ),(∀ j,1 ≤ r j) → (∀ j,0 < η j) → (∀ j,η j ≤ 1) →
      (∀ j,128 ≤ cn/(η j)^2) → (∀ j,0 < b j) → (∀ j,b j ≤ 1) → 1 ≤ CR → ζ*Real.sqrt cn ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (J m normals : ℕ) (index : Fin J → Fin normals) (d : ℝ),0 < d →
      ∀ z : Full (Joint E (Blocks m F)) normals,
      let N := fun i : Fin J => ((D (i.val+1) []).n:ℝ)+1
      let ell := fun i : Fin J => (D (i.val+1) []).ell
      let h := fun i : Fin J => (D (i.val+1) []).width
      ‖iteratedFDeriv ℝ 1 (sourceCoarseExtension m normals M D J index d) z‖ ≤
        ∑ i : Fin J,2*SmallGapLiftSupport.C*C^(J+2)*N i*ell i*(h i)^2/d ∧
      ‖iteratedFDeriv ℝ 2 (sourceCoarseExtension m normals M D J index d) z‖ ≤
        ∑ i : Fin J,4*SmallGapLiftSupport.C*C^(J+2)*ell i*h i*((N i)^(1/3:ℝ))^2/d ∧
      ‖iteratedFDeriv ℝ 3 (sourceCoarseExtension m normals M D J index d) z‖ ≤
        ∑ i : Fin J,8*SmallGapLiftSupport.C*C^(J+2)*ell i*(N i)^(1/3:ℝ)/d := by
  obtain ⟨C,hC,hledger⟩ := source_coarse_family_ledger A K ζ cn hA hK hζ hζ1 hcn hcn1
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  have hled := hledger E F n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  intro J m normals index d hd z
  let N := fun i : Fin J => ((D (i.val+1) []).n:ℝ)+1
  let ell := fun i : Fin J => (D (i.val+1) []).ell
  let h := fun i : Fin J => (D (i.val+1) []).width
  have hp (i : Fin J) := parentScale_positive initial r η hl hw hr hη (i.val+2)
  apply coarseSum_normalized_jets index (coarseFamily m M D J) N ell h (C^(J+2)) d
    (coarseFamily_contDiff m M D J)
    (fun i => by dsimp [N]; have hn := Nat.cast_nonneg (α:=ℝ) (D (i.val+1) []).n; linarith)
    (fun i => (hp i).1.le) (fun i => (hp i).2) (pow_nonneg (by linarith) _) hd
  intro i y
  have h0 := hled J m i y 0 (by norm_num)
  have h1 := hled J m i y 1 (by norm_num)
  have h2 := hled J m i y 2 (by norm_num)
  have h3 := hled J m i y 3 (by norm_num)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,ledgerScale] at h0 h1 h2 h3
  change _ ≤ C^(J+2)*N i*ell i*(h i)^2 ∧ _ ≤ C^(J+2)*ell i*h i*Real.sqrt (N i) ∧
    _ ≤ C^(J+2)*ell i ∧ _ ≤ C^(J+2)*ell i/h i
  refine ⟨?_,?_,h2,?_⟩
  · convert h0 using 1
    dsimp only [N,ell,h]
    ring
  · convert h1 using 1
    dsimp only [N,ell,h]
    ring
  · convert h3 using 1
    dsimp only [N,ell,h]
    ring

end Bilevel.ChiExtensionCalibration
