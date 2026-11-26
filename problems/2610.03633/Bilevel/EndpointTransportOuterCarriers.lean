import Bilevel.EndpointTransportOuterSelection
import Bilevel.EndpointTransportSelectedLedger
import Bilevel.ChiOuterCarrierLedger

/-! Actual one-sided macroP-selected physical carriers and their complete
source mixed-jet ledger, on any heterogeneous ambient normed space. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def outerPhysicalCarrier {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d t : ℕ) : X → ℝ :=
  macroSelected M macroP (fun i => physicalCarrier m Q G A B d 0 [i.val] t)

theorem outerPhysicalCarrier_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d t : ℕ) : ContDiff ℝ 3 (outerPhysicalCarrier m Q M macroP G A B d t) :=
  macroSelected_contDiff M macroP _ (fun i => physicalCarrier_contDiff m Q G A B d 0 [i.val] t)

theorem outer_physical_carrier_trace {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (d : ℕ) (x : X) :
    (∑ t : Fin (d+1),outerPhysicalCarrier m Q M macroP G A B d t.val x)=
      ∑ i : Fin (M.n+1),macroSelector M macroP i x*physicalRecursive Q G d 0 [i.val] (padded (A x)) (B x) := by
  unfold outerPhysicalCarrier macroSelected
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum,← physical_recursive_carrier_trace m Q G A B d 0 [i.val] x]

theorem source_outer_physical_ledger (Ar K ζ cn : ℝ) (hAr : 0≤Ar) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D nM : ℕ) (Q : Rotations n D) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space nM →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block D),
      let M := sourceMacroNode nM initial Km U
      let G := sourceGeometry initial r η b Ar K ζ cn CR V
      ∀ (m : ℕ) (macroP : X →L[ℝ] E) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),
      ‖macroP‖≤1 → ‖A‖≤1 → ‖B‖≤1 → ∀ (d t : ℕ),t≤d → ∀ (x : X) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (outerPhysicalCarrier m Q M macroP G A B d t) x‖≤
        C^(t+2)*ledgerScale (((G t []).n:ℝ)+1) (G t []).ell (G t []).width q := by
  obtain ⟨Ci,hCi,hinner⟩ := source_selected_physical_ledger Ar K ζ cn hAr hK hζ hζ1 hcn hcn1
  obtain ⟨Co,hCo,houter⟩ := constructed_macro_carrier_step
  let C := Ci+Co
  have hC : 1≤C := by dsimp [C];linarith
  have hCi0 : 0≤Ci := by linarith
  have hC0 : 0≤C := by linarith
  refine ⟨C,hC,fun E _ _ _ X _ _ n D nM Q initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V => ?_⟩
  dsimp only
  let M := sourceMacroNode nM initial Km U
  let G := sourceGeometry initial r η b Ar K ζ cn CR V
  have hp := parentScale_positive initial r η hl hw hr hη
  have hmono := parentScale_width_antitone initial r η hl hw hr hη hη1
  intro m macroP A B hmacro hA hB d t ht x q hq
  have hell : 0≤(G t []).ell := (hp (t+1)).1.le
  have hh : 0<(G t []).width := (hp (t+1)).2
  have hN : 1≤((G t []).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (G t []).n;linarith
  have hwidth : (G t []).width*Real.sqrt (((G t []).n:ℝ)+1)≤M.width :=
    (source_width_sqrt_length_le_parent hcn hcn1 (hη t) (hp t).2 (hr t) (hlen t)).trans
      (hmono (Nat.zero_le t))
  have hs := houter E X M macroP hmacro hw (sourceMacro_radius_ge_width hw hKm U)
    (fun i => physicalCarrier m Q G A B d 0 [i.val] t)
    (fun i => physicalCarrier_contDiff m Q G A B d 0 [i.val] t)
    (Ci^(t+1)) (((G t []).n:ℝ)+1) (G t []).ell (G t []).width (by positivity) hN hell hh hwidth x q hq
    (fun i k hk => by
      simpa only [Nat.zero_add] using
        (hinner X n D Q initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn V m A B hA hB d t 0 ht [i.val] x k (by omega)))
  have hcoeff : Co*Ci^(t+1)≤C^(t+2) := by
    calc
      _≤C*C^(t+1) := mul_le_mul (by dsimp [C];linarith)
        (pow_le_pow_left₀ hCi0 (by dsimp [C];linarith) _) (by positivity) hC0
      _=_ := by rw [show t+2=(t+1)+1 by omega,pow_succ];ring
  exact hs.trans (mul_le_mul_of_nonneg_right hcoeff (ledgerScale_nonneg (by positivity) hell hh.le q))

end Bilevel.EndpointTransportResponse

