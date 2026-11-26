import Bilevel.ChiOuterCarrierFineLedger

/-! Actual deepest revealed carrier A_J after subtraction of the complete
outer-and-inner selected centered frontier, with all mixed derivative orders. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerDeepestA (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) : Joint E (Blocks m F) → ℝ :=
  fun z => outerCarrier m M D d d z-outerFineFrontier m M D d z

theorem outerDeepestA_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) :
    ContDiff ℝ 3 (outerDeepestA m M D d) :=
  (outerCarrier_contDiff m M D d d).sub (outerFineFrontier_contDiff m M D d)

theorem frontierScale_le_ledger {N ℓ h : ℝ} (hN : 1≤N) (hℓ : 0≤ℓ) (hh : 0<h)
    (k : ℕ) (hk : k≤3) : fineScale (ℓ*h^2) (ℓ*h) h k≤ledgerScale N ℓ h k := by
  have he : fineScale (ℓ*h^2) (ℓ*h) h k=(ℓ*h^2)/h^k := by
    cases k with
    | zero => simp only [fineScale,pow_zero,div_one]
    | succ k => simp only [fineScale,pow_succ];field_simp;ring
  rw [he]
  exact residualScale_le_ledger hN hℓ hh k hk

theorem source_outer_deepest_A_ledger (A K ζ cn : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (d m : ℕ) (z : Joint E (Blocks m F)) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (outerDeepestA m M D d) z‖≤
        C^(d+2)*ledgerScale (((D d []).n:ℝ)+1) (D d []).ell (D d []).width q := by
  obtain ⟨Cc,hCc,hcarrier⟩ := source_outer_selected_ledger A K ζ cn hA hK hζ hζ1 hcn hcn1
  obtain ⟨Cf,hCf,hfine⟩ := source_outer_selected_fine_ledger
  have hCc0 : 0≤Cc := by linarith
  have hCf0 : 0≤Cf := by linarith
  refine ⟨Cc+Cf,by linarith,fun E F _ _ _ _ _ _ n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V => ?_⟩
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  have hc := hcarrier E F n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V
  have hf := hfine E F n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
  intro d m z q hq
  have hp := parentScale_positive initial r η hl hw hr hη (d+1)
  have hell : 0≤(D d []).ell := hp.1.le
  have hh : 0<(D d []).width := hp.2
  have hN : 1≤((D d []).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (D d []).n;linarith
  have hcq := hc d d m z q hq
  have hfq := (hf d m z q hq).1
  have hscale := mul_le_mul_of_nonneg_left (frontierScale_le_ledger hN hell hh q hq) (pow_nonneg hCf0 (d+2))
  have hbound := hfq.trans hscale
  have hs := ZeroChainResidualBounds.jet_sub_norm_le (outerCarrier_contDiff m M D d d)
    (outerFineFrontier_contDiff m M D d) z q hq
  have hcoeff := mul_le_mul_of_nonneg_right (pow_add_pow_le hCc0 hCf0 (by omega : d+2≠0))
    (ledgerScale_nonneg (N:=((D d []).n:ℝ)+1) (by positivity) hell hh.le q)
  apply hs.trans
  nlinarith only [hcq,hbound,hcoeff]

end Bilevel.ChiOuter
