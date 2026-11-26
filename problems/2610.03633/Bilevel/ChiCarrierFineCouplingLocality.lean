import Bilevel.ChiCarrierInactivePieceLocality
import Bilevel.ChiCarrierFineCoupling

/-! Actual active and fixed inactive selected fine couplings at arbitrary
normal arguments. Every ancestor and every radial query direction is
included in the finite disclosed space. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def TreeBlind {m : ℕ} (D : Geometry E) (j d : ℕ) (hm : j+d < m)
    (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ) : Prop :=
  ∀ k P (_hk : j ≤ k) (hkt : k ≤ j+d),BlindNode W x ⟨k,by omega⟩ (D k P) (r k P)

theorem selectedCoupling_slice_eq (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ s : ℝ) (x : Blocks m E) :
    selectedCoupling m D d j I c θ (CompensatedMean.pack (Blocks m E) x s 0)=
      ∑ p ∈ Finset.range (levels θ+1),selectedFinePiece m D d j I c θ p x*
        SmallGapProfiles.normal (width c (D (j+d) []).width θ p) s := by
  simp only [selectedCoupling,CompensatedMean.uProj_pack,CompensatedMean.sProj_pack]

theorem selectedCoupling_tangent_support {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j d hm W x r)
    (c θ s : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D (j+d) P).ell)
    (hnew : ∀ P,∀ k : Fin ((D (j+d) P).n+1),k.val=r (j+d) P →
      (D (j+d) P).frame (basis k)∈W ⟨j+d,hm⟩) :
    gradient (fun y => selectedCoupling m D d j I c θ
      (CompensatedMean.pack (Blocks m E) y s 0)) x∈knownSpace W := by
  rw [show (fun y => selectedCoupling m D d j I c θ (CompensatedMean.pack (Blocks m E) y s 0))=
    (fun y => ∑ p ∈ Finset.range (levels θ+1),selectedFinePiece m D d j I c θ p y*
      SmallGapProfiles.normal (width c (D (j+d) []).width θ p) s) from funext
        (selectedCoupling_slice_eq m D d j I c θ s)]
  apply gradient_sum_mem _ (knownSpace W) _
    (fun p => (selectedFinePiece_contDiff m D d j I c θ p).mul contDiff_const)
  intro p _
  apply gradient_mul_mem (knownSpace W) (selectedFinePiece_contDiff m D d j I c θ p) contDiff_const x
  · apply selectedFinePiece_gradient_mem D d j I hm W x r
      (fun k P hk hkt => htree k P hk (by omega)) c θ hc hcs hθ hell
      (fun P => (htree (j+d) P (by omega) le_rfl).width_pos)
      (fun P => (htree (j+d) P (by omega) le_rfl).radius_pos)
      (htree (j+d) [] (by omega) le_rfl).query_mem
      _ (fun P => (htree (j+d) P (by omega) le_rfl).blind) p
    intro P k hk
    by_cases hkr : k.val < r (j+d) P
    · exact (htree (j+d) P (by omega) le_rfl).columns_mem k hkr
    · exact hnew P k (by omega)
  · exact gradient_const_mem (knownSpace W) _ _

def selectedInactiveCoupling (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ)
    (y : CompensatedMean.LowerSpace (Blocks m E)) : ℝ :=
  let W := width c (D (j+d) []).width θ (levels θ)
  selectedCoupling m D d j I c θ y-selectedFineSignal m D d j I (W/8) (CompensatedMean.uProj _ y)*
    SmallGapProfiles.normal W (CompensatedMean.sProj _ y)

theorem selectedInactiveCoupling_slice_eq (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ s : ℝ) (x : Blocks m E) :
    selectedInactiveCoupling m D d j I c θ (CompensatedMean.pack (Blocks m E) x s 0)=
      ∑ p ∈ Finset.range (levels θ+1),selectedInactivePiece m D d j I c θ
        (width c (D (j+d) []).width θ (levels θ)/8) p x*
        SmallGapProfiles.normal (width c (D (j+d) []).width θ p) s := by
  simp only [selectedInactivePiece_eq,sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,
    Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_self,if_true]
  rw [← selectedCoupling_slice_eq m D d j I c θ s x]
  simp only [selectedInactiveCoupling,CompensatedMean.uProj_pack,CompensatedMean.sProj_pack]

theorem selectedInactiveCoupling_tangent_support {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j d hm W x r)
    (c θ s : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D (j+d) P).ell)
    (hwidth : ∀ P,(D (j+d) P).width=(D (j+d) []).width)
    (hz : ∀ P,∀ k : Fin ((D (j+d) P).n+1),r (j+d) P ≤ k.val →
      |(D (j+d) P).coordinates (x ⟨j+d,hm⟩) k|≤
        width c (D (j+d) []).width θ (levels θ)/8) :
    gradient (fun y => selectedInactiveCoupling m D d j I c θ
      (CompensatedMean.pack (Blocks m E) y s 0)) x∈knownSpace W := by
  rw [show (fun y => selectedInactiveCoupling m D d j I c θ (CompensatedMean.pack (Blocks m E) y s 0))=
    (fun y => ∑ p ∈ Finset.range (levels θ+1),selectedInactivePiece m D d j I c θ
      (width c (D (j+d) []).width θ (levels θ)/8) p y*
      SmallGapProfiles.normal (width c (D (j+d) []).width θ p) s) from funext
        (selectedInactiveCoupling_slice_eq m D d j I c θ s)]
  apply gradient_sum_mem _ (knownSpace W) _
    (fun p => (selectedInactivePiece_contDiff m D d j I c θ _ p).mul contDiff_const)
  intro p hp
  apply gradient_mul_mem (knownSpace W) (selectedInactivePiece_contDiff m D d j I c θ _ p) contDiff_const x
  · exact selectedInactivePiece_gradient_mem D d j I hm W x r
      (fun k P hk hkt => htree k P hk (by omega)) c θ _ hc hcs hθ hell
      (fun P => (htree (j+d) P (by omega) le_rfl).width_pos)
      (fun P => (htree (j+d) P (by omega) le_rfl).radius_pos)
      (fun P => by rw [hwidth P]) (htree (j+d) [] (by omega) le_rfl).query_mem
      (fun P => (htree (j+d) P (by omega) le_rfl).columns_mem) hz p
      (by have := Finset.mem_range.mp hp;omega)
  · exact gradient_const_mem (knownSpace W) _ _

end Bilevel.ChiCarrier
