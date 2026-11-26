import Bilevel.ChiOuterCarrierDeepest
import Bilevel.ChiExtensionTerms

/-! The actual finite coarse family in the source hidden extension:
the intermediate selected carriers and the last revealed carrier A_J.
All mixed tangential derivatives are supplied by the constructed ledgers. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def coarseFamily (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ) (i : Fin J) :
    Joint E (Blocks m F) → ℝ :=
  if i.val+1 = J then outerDeepestA m M D J else outerCarrier m M D J (i.val+1)

theorem coarseFamily_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ) (i : Fin J) :
    ContDiff ℝ 3 (coarseFamily m M D J i) := by
  unfold coarseFamily
  split_ifs
  · exact outerDeepestA_contDiff m M D J
  · exact outerCarrier_contDiff m M D J (i.val+1)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem source_coarse_family_ledger (A K ζ cn : ℝ) (hA : 0 ≤ A) (hK : 1 ≤ K)
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
      ∀ (J m : ℕ) (i : Fin J) (z : Joint E (Blocks m F)) (q : ℕ),q ≤ 3 →
      ‖iteratedFDeriv ℝ q (coarseFamily m M D J i) z‖ ≤
        C^(J+2)*ledgerScale (((D (i.val+1) []).n:ℝ)+1) (D (i.val+1) []).ell (D (i.val+1) []).width q := by
  obtain ⟨Cc,hCc,hcarrier⟩ := source_outer_selected_ledger A K ζ cn hA hK hζ hζ1 hcn hcn1
  obtain ⟨Ca,hCa,hdeep⟩ := source_outer_deepest_A_ledger A K ζ cn hA hK hζ hζ1 hcn hcn1
  let C := Cc+Ca
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCcC : Cc ≤ C := by dsimp [C]; linarith
  have hCaC : Ca ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  have hc := hcarrier E F n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  have ha := hdeep E F n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  intro J m i z q hq
  have hp := parentScale_positive initial r η hl hw hr hη (i.val+2)
  have hscale : 0 ≤ ledgerScale (((D (i.val+1) []).n:ℝ)+1)
      (D (i.val+1) []).ell (D (i.val+1) []).width q :=
    ledgerScale_nonneg (by positivity) hp.1.le hp.2.le q
  change ‖iteratedFDeriv ℝ q (coarseFamily m M D J i) z‖ ≤ _
  unfold coarseFamily
  split_ifs with he
  · have hh := ha J m z q hq
    have hcoeff := pow_le_pow_left₀ (show 0 ≤ Ca by linarith) hCaC (J+2)
    rw [he] at hscale ⊢
    exact hh.trans (mul_le_mul_of_nonneg_right hcoeff hscale)
  · have hh := hc J (i.val+1) m z q hq
    have hcoeff := (pow_le_pow_left₀ (show 0 ≤ Cc by linarith) hCcC (i.val+1+2)).trans
      (pow_le_pow_right₀ hC (by omega : i.val+1+2 ≤ J+2))
    exact hh.trans (mul_le_mul_of_nonneg_right hcoeff hscale)

theorem coarseFamily_normal_jets (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ) (i : Fin J)
    {C : ℝ} (hC : 0 ≤ C) (hell : 0 ≤ (D (i.val+1) []).ell) (hh : 0 < (D (i.val+1) []).width)
    (hb : ∀ z q,q ≤ 3 → ‖iteratedFDeriv ℝ q (coarseFamily m M D J i) z‖ ≤
      C^(J+2)*ledgerScale (((D (i.val+1) []).n:ℝ)+1) (D (i.val+1) []).ell (D (i.val+1) []).width q)
    (k : ℕ) (normalIndex : Fin k) (z : Full (Joint E (Blocks m F)) k) :
    let N := ((D (i.val+1) []).n:ℝ)+1
    let ℓ := (D (i.val+1) []).ell
    let h := (D (i.val+1) []).width
    let f := normalTerm k normalIndex (coarseFamily m M D J i) (h*N^(1/3:ℝ))
    ‖iteratedFDeriv ℝ 1 f z‖ ≤ 2*SmallGapLiftSupport.C*C^(J+2)*N*ℓ*h^2 ∧
    ‖iteratedFDeriv ℝ 2 f z‖ ≤ 4*SmallGapLiftSupport.C*C^(J+2)*ℓ*h*(N^(1/3:ℝ))^2 ∧
    ‖iteratedFDeriv ℝ 3 f z‖ ≤ 8*SmallGapLiftSupport.C*C^(J+2)*ℓ*N^(1/3:ℝ) := by
  dsimp only
  apply normalTerm_coarse_jets k normalIndex (coarseFamily_contDiff m M D J i)
    (by have hn := Nat.cast_nonneg (α:=ℝ) (D (i.val+1) []).n; linarith) hell hh (pow_nonneg hC _)
  intro y
  have h0 := hb y 0 (by norm_num)
  have h1 := hb y 1 (by norm_num)
  have h2 := hb y 2 (by norm_num)
  have h3 := hb y 3 (by norm_num)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,ledgerScale] at h0 h1 h2 h3
  refine ⟨?_,?_,h2,?_⟩
  · convert h0 using 1
    ring
  · convert h1 using 1
    ring
  · convert h3 using 1
    ring

end Bilevel.ChiExtensionCalibration
