import Bilevel.EndpointTransportLocalLedger
import Bilevel.ChiCarrierSourceWidths

/-! Complete selected-carrier ledger for the actual source transport family,
including every ancestor mixed derivative and all terminal physical terms. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem physicalCarrier_selectFamily {n D : ℕ} (m : ℕ) (Q : Rotations n D) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d t j : ℕ) (I : List ℕ) :
    physicalCarrier m Q G A B (d+t) j I t=
      ChiLiftedCarrier.selectFamily m G A (fun j I => physicalCarrier m Q G A B d j I 0) t j I := by
  induction t generalizing j I with
  | zero => rfl
  | succ t ih =>
    funext x
    change (∑ i : Fin ((G j I).n+1),ChiLiftedCarrier.selector m j (G j I) A i x*
      physicalCarrier m Q G A B (d+t) (j+1) (child I i.val) t x)=_
    simp only [ChiLiftedCarrier.selectFamily]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih]

theorem source_selected_physical_ledger (Ar K ζ cn : ℝ) (hAr : 0≤Ar) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) : ∃ C : ℝ,1≤C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D : ℕ) (Q : Rotations n D) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block D),
      let G := sourceGeometry initial r η b Ar K ζ cn CR U
      ∀ (m : ℕ) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (d t j : ℕ),t≤d → ∀ (I : List ℕ) (x : X) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (physicalCarrier m Q G A B d j I t) x‖≤
        C^(t+1)*ledgerScale (((G (j+t) []).n:ℝ)+1) (G (j+t) []).ell (G (j+t) []).width k := by
  obtain ⟨Cb,hCb,hbase⟩ := source_physical_local_ledger Ar K ζ cn hAr hK hζ hζ1 hcn
  obtain ⟨Cs,hCs,hsel⟩ := ChiLiftedCarrier.constructed_ledger_selection_bound
  let C := Cb+Cs
  have hC : 1≤C := by dsimp [C];linarith
  have hCb0 : 0≤Cb := by linarith
  have hCs0 : 0≤Cs := by linarith
  have hC0 : 0≤C := by linarith
  refine ⟨C,hC,fun X _ _ n D Q initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn U => ?_⟩
  dsimp only
  let G := sourceGeometry initial r η b Ar K ζ cn CR U
  have hp := parentScale_positive initial r η hl hw hr hη
  have hadm (j : ℕ) (I : List ℕ) : NodeJetAdmissible (G j I) :=
    sourceNode_admissible Ar K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hp j).1 (hp j).2 (hr j) (hb j) (hb1 j)
  have hwidth := source_geometry_ancestor_width initial r η b Ar K ζ cn CR U
    hl hw hr hη hη1 hcn hcn1 hlen
  intro m A B hA hB d t j ht I x k hk
  have hd := hadm (j+t) []
  have hN : 1≤((G (j+t) []).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (G (j+t) []).n;linarith
  have hb₀ (J : List ℕ) (y : X) (q : ℕ) (hq : q≤3) :=
    hbase X n D Q initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn U m A B hA hB (d-t) (j+t) J y q hq
  have hs := hsel (Block D) X m G A hA hadm
    (fun j I => physicalCarrier m Q G A B (d-t) j I 0)
    (fun j I => physicalCarrier_contDiff m Q G A B (d-t) j I 0)
    (j+t) Cb (((G (j+t) []).n:ℝ)+1) (G (j+t) []).ell (G (j+t) []).width
    hCb0 hN hd.1 hd.2.1 (fun l J hl => hwidth l (j+t) hl J []) hb₀ t j rfl I x k hk
  rw [← physicalCarrier_selectFamily] at hs
  rw [Nat.sub_add_cancel ht] at hs
  have hcoef : Cs^t*Cb≤C^(t+1) := by
    calc
      _≤C^t*C := mul_le_mul (pow_le_pow_left₀ hCs0 (by dsimp [C];linarith) t)
        (by dsimp [C];linarith) hCb0 (pow_nonneg hC0 t)
      _=_ := (pow_succ C t).symm
  exact hs.trans (mul_le_mul_of_nonneg_right hcoef (ledgerScale_nonneg (by positivity) hd.1 hd.2.1.le k))

end Bilevel.EndpointTransportResponse
