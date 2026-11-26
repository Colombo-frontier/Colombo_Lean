import Bilevel.ChiCarrierProductLedger
import Bilevel.ChiRecursiveSourceGeometry

/-! Complete actual local carrier ledger, including joint release terms
and centered leaves, for the source's recursively generated node family. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

theorem residualScale_le_ledger {N ℓ h : ℝ} (hN : 1≤N) (hℓ : 0≤ℓ) (hh : 0<h)
    (k : ℕ) (hk : k≤3) : (ℓ*h^2)/h^k≤ledgerScale N ℓ h k := by
  have hs : 1≤Real.sqrt N := Real.one_le_sqrt.mpr hN
  interval_cases k
  · simp only [ledgerScale,pow_zero,div_one]
    nlinarith only [mul_le_mul_of_nonneg_right hN (show 0≤ℓ*h^2 by positivity)]
  · have he : ℓ*h^2/h^1=ℓ*h := by field_simp;ring
    rw [he]
    simpa only [ledgerScale,mul_one] using mul_le_mul_of_nonneg_left hs (show 0≤ℓ*h by positivity)
  · have he : ℓ*h^2/h^2=ℓ := by field_simp
    rw [he]
    rfl
  · have he : ℓ*h^2/h^3=ℓ/h := by field_simp;ring
    rw [he]
    rfl

theorem source_geometry_local_ledger (A K ζ cn : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) :
    ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let D := sourceGeometry initial r η b A K ζ cn CR U
      ∀ (d j : ℕ) (I : List ℕ) (m : ℕ) (x : Blocks m F) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (jointCarrier m D d j I 0) x‖≤
        C*ledgerScale (((D j I).n:ℝ)+1) (D j I).ell (D j I).width k := by
  obtain ⟨Ch,hCh,hH⟩ := sourceNode_joint_ledger A K ζ cn hA hK hζ hζ1 hcn
  obtain ⟨Cr,hCr,hrelease⟩ := constructed_release_correction_jets
  have hCh0 : 0≤Ch := by linarith
  have hCr0 : 0≤Cr := by linarith
  let C := 2*Ch+Cr
  have hC : 1≤C := by unfold C;linarith
  refine ⟨C,hC,fun F _ _ _ initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn U => ?_⟩
  dsimp only
  let D := sourceGeometry initial r η b A K ζ cn CR U
  have hp := parentScale_positive initial r η hl hw hr hη
  have hadm (j : ℕ) (I : List ℕ) :
      0≤(D j I).ell ∧ 0<(D j I).width ∧ (D j I).width≤(D j I).radius ∧
      0<(D j I).parentWidth ∧ (D j I).parentWidth≤(D j I).radius :=
    sourceNode_admissible A K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hp j).1 (hp j).2 (hr j) (hb j) (hb1 j)
  have hlocalH (m j : ℕ) (I : List ℕ) (x : Blocks m F) (k : ℕ) (hk : k≤3) :
      ‖iteratedFDeriv ℝ k (jointH m j (D j I)) x‖≤
        Ch*ledgerScale (((D j I).n:ℝ)+1) (D j I).ell (D j I).width k :=
    hH F (η j) CR _ _ (r j) (b j) (hη j) (hη1 j) (hlen j) hCR hCRcn
      (hp j).1 (hp j).2 (hr j) (hb j) (hb1 j) (U j I) m j x k hk
  intro d j I m x k hk
  have hd := hadm j I
  have hN : 1≤((D j I).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (D j I).n;linarith
  have hS : 0≤ledgerScale (((D j I).n:ℝ)+1) (D j I).ell (D j I).width k :=
    ledgerScale_nonneg (by positivity) hd.1 hd.2.1.le k
  cases d with
  | zero =>
    have hconst : ‖iteratedFDeriv ℝ k (fun _ : Blocks m F => (D j I).H 0) x‖≤
        Ch*ledgerScale (((D j I).n:ℝ)+1) (D j I).ell (D j I).width k := by
      by_cases hk0 : k=0
      · subst k
        have hz := hlocalH m j I 0 0 (by norm_num)
        simpa only [norm_iteratedFDeriv_zero,jointH,Function.comp_apply,map_zero] using hz
      · rw [iteratedFDeriv_const_of_ne hk0,Pi.zero_apply,norm_zero]
        exact mul_nonneg hCh0 hS
    have hs := ZeroChainResidualBounds.jet_sub_norm_le (g:=fun _ : Blocks m F => (D j I).H 0)
      (jointH_contDiff m j (D j I) 3) contDiff_const x k hk
    apply hs.trans
    have h₁ := hlocalH m j I x k hk
    have h₂ := mul_nonneg hCr0 hS
    unfold C
    nlinarith only [h₁,hconst,h₂]
  | succ d =>
    rw [jointCarrier_local_formula]
    have hc := hrelease F (D j I) (fun i => D (j+1) (child I i.val))
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
      (fun i => (hadm (j+1) (child I i.val)).1)
      (fun i => (hadm (j+1) (child I i.val)).2.1)
      (fun i => (hadm (j+1) (child I i.val)).2.2.1)
      (fun _ => rfl) (fun i => (hadm (j+1) (child I i.val)).2.2.2.2) m j x k hk
    have hscale := mul_le_mul_of_nonneg_left (residualScale_le_ledger hN hd.1 hd.2.1 k hk) hCr0
    have hc' : ‖iteratedFDeriv ℝ k
        (releaseCorrection m j (D j I) (fun i => D (j+1) (child I i.val))) x‖≤
        Cr*ledgerScale (((D j I).n:ℝ)+1) (D j I).ell (D j I).width k := by
      exact hc.trans (by simpa only [mul_div_assoc] using hscale)
    rw [iteratedFDeriv_add_apply'
      ((jointH_contDiff m j (D j I) 3).of_le (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk)).contDiffAt
      ((releaseCorrection_contDiff m j (D j I) (fun i => D (j+1) (child I i.val))).of_le
        (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk)).contDiffAt]
    apply (norm_add_le _ _).trans
    have h₁ := hlocalH m j I x k hk
    have h₂ := mul_nonneg hCh0 hS
    unfold C
    nlinarith only [h₁,hc',h₂]

end Bilevel.ChiCarrier
