import Bilevel.EndpointTransportCarriers
import Bilevel.ChiCarrierLocalLedger

/-! Full source ledger for the actual physical local carriers: centered
terminal payload, modified predecessor release, and unchanged ordinary terms. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier

theorem source_physical_local_ledger (Ar K ζ cn : ℝ) (hAr : 0≤Ar) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) : ∃ C : ℝ,1≤C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D : ℕ) (Q : Rotations n D) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block D),
      let G := sourceGeometry initial r η b Ar K ζ cn CR U
      ∀ (m : ℕ) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (d j : ℕ) (I : List ℕ) (x : X) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalCarrier m Q G A B d j I 0) x‖≤
        C*ledgerScale (((G j I).n:ℝ)+1) (G j I).ell (G j I).width k := by
  obtain ⟨Co,hCo,ho⟩ := source_geometry_local_ledger Ar K ζ cn hAr hK hζ hζ1 hcn
  obtain ⟨Ch,hCh,hh⟩ := sourceNode_joint_ledger Ar K ζ cn hAr hK hζ hζ1 hcn
  obtain ⟨Cp,hCp,hp⟩ := physical_source_ledger Ar K ζ cn hAr hK hζ hζ1 hcn
  obtain ⟨Cr,hCr,hrc⟩ := physical_release_correction_jets
  let C := Co+Ch+2*Cp+Cr
  have hC : 1≤C := by dsimp [C];linarith
  have hCo0 : 0≤Co := by linarith
  have hCh0 : 0≤Ch := by linarith
  have hCp0 : 0≤Cp := by linarith
  have hCr0 : 0≤Cr := by linarith
  refine ⟨C,hC,fun X _ _ n D Q initial hl hw r η b CR hrr hη hη1 hlen hb hb1 hCR hCRcn U => ?_⟩
  dsimp only
  let G := sourceGeometry initial r η b Ar K ζ cn CR U
  have hpos := parentScale_positive initial r η hl hw hrr hη
  have hadm (j : ℕ) (I : List ℕ) : NodeJetAdmissible (G j I) :=
    sourceNode_admissible Ar K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hpos j).1 (hpos j).2 (hrr j) (hb j) (hb1 j)
  intro m A B hA hB d j I x k hk
  have hd := hadm j I
  have hN : 1≤((G j I).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (G j I).n;linarith
  have hS : 0≤ledgerScale (((G j I).n:ℝ)+1) (G j I).ell (G j I).width k :=
    ledgerScale_nonneg (by positivity) hd.1 hd.2.1.le k
  have hphysical (Y : Physical n D) (q : ℕ) (hq : q≤3) :
      ‖iteratedFDeriv ℝ q (physicalPayload Q (G j I)) Y‖≤
        Cp*ledgerScale (((G j I).n:ℝ)+1) (G j I).ell (G j I).width q :=
    hp n D Q (η j) CR _ _ (r j) (b j) (hη j) (hη1 j) (hlen j) hCR hCRcn
      (hpos j).1 (hpos j).2 (hrr j) (hb j) (hb1 j) (U j I) Y q hq
  cases d with
  | zero =>
    have hconst : ‖iteratedFDeriv ℝ k (fun _ : X => (G j I).H 0) x‖≤
        Cp*ledgerScale (((G j I).n:ℝ)+1) (G j I).ell (G j I).width k := by
      by_cases hk0 : k=0
      · subst k
        have hz := hphysical 0 0 (by norm_num)
        simpa only [norm_iteratedFDeriv_zero,physical_payload_zero] using hz
      · rw [iteratedFDeriv_const_of_ne hk0,Pi.zero_apply,norm_zero]
        exact mul_nonneg hCp0 hS
    have hfirst := (linear_jet_contraction B hB (physical_payload_contDiff Q (G j I) 3) x k hk).trans
      (hphysical (B x) k hk)
    have hs := ZeroChainResidualBounds.jet_sub_norm_le
      (g:=fun _ : X => (G j I).H 0) ((physical_payload_contDiff Q (G j I) 3).comp B.contDiff) contDiff_const x k hk
    apply hs.trans
    have hcoef : 2*Cp≤C := by dsimp [C];linarith
    have hbound := mul_le_mul_of_nonneg_right hcoef hS
    nlinarith only [hfirst,hconst,hbound]
  | succ d =>
    by_cases hd0 : d=0
    · simp only [physicalCarrier,if_pos hd0]
      have hH := (linear_jet_contraction A hA (jointH_contDiff m j (G j I) 3) x k hk).trans
        (hh (Block D) (η j) CR _ _ (r j) (b j) (hη j) (hη1 j) (hlen j) hCR hCRcn
          (hpos j).1 (hpos j).2 (hrr j) (hb j) (hb1 j) (U j I) m j (A x) k hk)
      change ‖iteratedFDeriv ℝ k (jointH m j (G j I) ∘ A) x‖≤
        Ch*ledgerScale (((G j I).n:ℝ)+1) (G j I).ell (G j I).width k at hH
      have hc := hrc X n D m j (G j I) (fun i => G (j+1) (child I i.val)) hd
        (fun i => hadm (j+1) (child I i.val)) (fun _ => rfl) A B hA hB Q x k hk
      have hscale := mul_le_mul_of_nonneg_left (residualScale_le_ledger hN hd.1 hd.2.1 k hk) hCr0
      have hc' : ‖iteratedFDeriv ℝ k (physicalReleaseCorrection m j (G j I)
          (fun i => G (j+1) (child I i.val)) A B Q) x‖≤
          Cr*ledgerScale (((G j I).n:ℝ)+1) (G j I).ell (G j I).width k :=
        hc.trans (by simpa only [mul_div_assoc] using hscale)
      unfold lastParentCarrier
      change ‖iteratedFDeriv ℝ k (fun y => (jointH m j (G j I) ∘ A) y+
        physicalReleaseCorrection m j (G j I) (fun i => G (j+1) (child I i.val)) A B Q y) x‖≤_
      rw [iteratedFDeriv_add_apply'
        (((jointH_contDiff m j (G j I) 3).comp A.contDiff).of_le
          (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk)).contDiffAt
        ((physicalReleaseCorrection_contDiff m j (G j I) (fun i => G (j+1) (child I i.val)) A B Q).of_le
          (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk)).contDiffAt]
      apply (norm_add_le _ _).trans
      have hcoef : Ch+Cr≤C := by dsimp [C];linarith
      have hbound := mul_le_mul_of_nonneg_right hcoef hS
      nlinarith only [hH,hc',hbound]
    · simp only [physicalCarrier,if_neg hd0]
      exact ((linear_jet_contraction A hA (jointCarrier_contDiff m G (d+1) j I 0 3) x k hk).trans
        (ho (Block D) initial hl hw r η b CR hrr hη hη1 hlen hb hb1 hCR hCRcn U (d+1) j I m (A x) k hk)).trans
          (mul_le_mul_of_nonneg_right (show Co≤C by dsimp [C];linarith) hS)

end Bilevel.EndpointTransportResponse
