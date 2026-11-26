import Bilevel.EndpointTransportCoarseCarriers

/-! All actual physical coarse-carrier budgets, including the deepest
frontier subtraction, in the manuscript's source ledger and source scales. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier

theorem source_physical_coarse_ledger (Ar K ζ cn : ℝ) (hAr : 0≤Ar) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) : ∃ C : ℝ,1≤C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D : ℕ) (Q : Rotations n D) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block D),
      let G := sourceGeometry initial r η b Ar K ζ cn CR U
      ∀ (m : ℕ) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (d j : ℕ) (I : List ℕ) (P : ChiFine.Parameters),P.ℓ=(G (j+d) []).ell → P.β=(G (j+d) []).width →
      ∀ (t : ℕ),t≤d → ∀ (x : X) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalCoarseCarrier m Q G A B P d j I t) x‖≤
        C^(t+1)*ledgerScale (((G (j+t) []).n:ℝ)+1) (G (j+t) []).ell (G (j+t) []).width k := by
  obtain ⟨Cc,hCc,hc⟩ := source_selected_physical_ledger Ar K ζ cn hAr hK hζ hζ1 hcn hcn1
  obtain ⟨Cf,hCf,hf⟩ := selected_physical_frontier_ledger
  let C := 2*(Cc+Cf)
  have hC : 1≤C := by dsimp [C];linarith
  have hCc0 : 0≤Cc := by linarith
  have hCf0 : 0≤Cf := by linarith
  have hC0 : 0≤C := by linarith
  have hCcC : Cc≤C := by dsimp [C];linarith
  have hsum (t : ℕ) : Cc^(t+1)+Cf^(t+1)≤C^(t+1) := by
    have hp₁ := pow_le_pow_left₀ hCc0 (show Cc≤Cc+Cf by linarith) (t+1)
    have hp₂ := pow_le_pow_left₀ hCf0 (show Cf≤Cc+Cf by linarith) (t+1)
    have ht : (2:ℝ)≤2^(t+1) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 1≤t+1)
    have hh := mul_le_mul_of_nonneg_right ht (show 0≤(Cc+Cf)^(t+1) by positivity)
    dsimp [C]
    rw [mul_pow]
    linarith only [hp₁,hp₂,hh]
  refine ⟨C,hC,fun X _ _ n D Q initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn U => ?_⟩
  dsimp only
  let G := sourceGeometry initial r η b Ar K ζ cn CR U
  have hp := parentScale_positive initial r η hl hw hr hη
  have hadm (j : ℕ) (I : List ℕ) : NodeJetAdmissible (G j I) :=
    sourceNode_admissible Ar K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hp j).1 (hp j).2 (hr j) (hb j) (hb1 j)
  have hmono := parentScale_width_antitone initial r η hl hw hr hη hη1
  intro m A B hA hB d j I P hℓ hβ t ht x k hk
  have hcar := hc X n D Q initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn U m A B hA hB d t j ht I x k hk
  have hd := hadm (j+t) []
  have hN : 1≤((G (j+t) []).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (G (j+t) []).n;linarith
  have hS := ledgerScale_nonneg (N:=((G (j+t) []).n:ℝ)+1) (by positivity) hd.1 hd.2.1.le k
  change ‖iteratedFDeriv ℝ k (fun y => physicalCarrier m Q G A B d j I t y-
    if t=d then selectedPhysicalFineFrontier m G A B Q P d j I y else 0) x‖≤_
  by_cases htd : t=d
  · subst t
    have hfine := hf X n D m G hadm A B hA hB Q P d j I
      (fun l J hl => by rw [hβ];exact hmono (by omega : l+1≤j+d+1))
      (fun J => by rw [hβ];exact (hadm (j+d) J).2.2.1) x k hk
    have hscale := fineScale_le_ledger hN hd.1 hd.2.1 k hk
    have hfine' : ‖iteratedFDeriv ℝ k (selectedPhysicalFineFrontier m G A B Q P d j I) x‖≤
        Cf^(d+1)*ledgerScale (((G (j+d) []).n:ℝ)+1) (G (j+d) []).ell (G (j+d) []).width k := by
      apply hfine.trans
      dsimp only [ChiFine.Parameters.amplitude]
      rw [hℓ,hβ]
      exact mul_le_mul_of_nonneg_left hscale (pow_nonneg hCf0 _)
    simp only [physicalCoarseCarrier,if_pos rfl]
    have hs := ZeroChainResidualBounds.jet_sub_norm_le (physicalCarrier_contDiff m Q G A B d j I d)
      (selectedPhysicalFineFrontier_contDiff m G A B Q P d j I) x k hk
    apply hs.trans
    have hc := mul_le_mul_of_nonneg_right (hsum d) hS
    linarith only [hcar,hfine',hc]
  · simp only [physicalCoarseCarrier,if_neg htd,sub_zero]
    exact hcar.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCc0 hCcC (t+1)) hS)

end Bilevel.EndpointTransportResponse
