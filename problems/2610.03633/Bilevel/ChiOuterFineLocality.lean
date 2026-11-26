import Bilevel.ChiOuterCoarseLocality
import Bilevel.ChiOuterCarrierInactive

/-! The actual outer-selected active and globally fixed inactive fine
extensions have inner support at every normal argument. The outer macro
is fixed, exactly as in the nonlinear lower inverse problem. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem selectedCoupling_slice_contDiff (m : ℕ) (D : Geometry F) (d j : ℕ) (I : List ℕ)
    (c θ s : ℝ) : ContDiff ℝ 3 (fun x => selectedCoupling m D d j I c θ
      (CompensatedMean.pack (Blocks m F) x s 0)) := by
  rw [funext (selectedCoupling_slice_eq m D d j I c θ s)]
  exact ContDiff.sum (fun p _ => (selectedFinePiece_contDiff m D d j I c θ p).mul contDiff_const)

theorem selectedInactiveCoupling_slice_contDiff (m : ℕ) (D : Geometry F) (d j : ℕ) (I : List ℕ)
    (c θ s : ℝ) : ContDiff ℝ 3 (fun x => selectedInactiveCoupling m D d j I c θ
      (CompensatedMean.pack (Blocks m F) x s 0)) := by
  rw [funext (selectedInactiveCoupling_slice_eq m D d j I c θ s)]
  exact ContDiff.sum (fun p _ => (selectedInactivePiece_contDiff m D d j I c θ _ p).mul contDiff_const)

theorem outerCoupling_inner_eq (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ)
    (c θ s : ℝ) (a : E) (x : Blocks m F) :
    outerCoupling m M D d c θ (CompensatedMean.pack (Joint E (Blocks m F)) (pack a x) s 0)=
      outerSelected m M (fun i y => selectedCoupling m D d 0 [i.val] c θ
        (CompensatedMean.pack (Blocks m F) y s 0)) (pack a x) := by
  simp only [outerCoupling,CompensatedMean.uProj_pack,CompensatedMean.sProj_pack,
    outerFinePiece,outerSelected,selectedCoupling_slice_eq,zero_add,
    Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem outerCoupling_inner_support {m : ℕ} (M : Node E) (D : Geometry F) (d : ℕ)
    (hm : d < m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (r : ℕ → List ℕ → ℕ) (htree : TreeBlind D 0 d (by simpa using hm) W x r)
    (c θ s : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D d P).ell)
    (hnew : ∀ P,∀ k : Fin ((D d P).n+1),k.val=r d P → (D d P).frame (basis k)∈W ⟨d,hm⟩) :
    gradient (fun y => outerCoupling m M D d c θ
      (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) s 0)) x∈knownSpace W := by
  rw [funext (outerCoupling_inner_eq m M D d c θ s a)]
  apply outerSelected_inner_gradient_mem m M _
    (fun i => selectedCoupling_slice_contDiff m D d 0 [i.val] c θ s) a x (knownSpace W)
  intro i
  have hnew' (t : ℕ) (ht : t=d) : ∀ P,∀ k : Fin ((D t P).n+1),k.val=r t P →
      (D t P).frame (basis k)∈W ⟨t,by omega⟩ := by
    subst t
    exact hnew
  exact selectedCoupling_tangent_support D d 0 [i.val] (by simpa using hm) W x r htree
    c θ s hc hcs hθ (by simpa only [zero_add] using hell) (hnew' (0+d) (Nat.zero_add d))

def outerInactiveCoupling (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (y : CompensatedMean.LowerSpace (Joint E (Blocks m F))) : ℝ :=
  let W := width c (D d []).width θ (levels θ)
  outerCoupling m M D d c θ y-outerFineSignal m M D d (W/8) (CompensatedMean.uProj _ y)*
    SmallGapProfiles.normal W (CompensatedMean.sProj _ y)

theorem outerInactiveCoupling_inner_eq (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ)
    (c θ s : ℝ) (a : E) (x : Blocks m F) :
    outerInactiveCoupling m M D d c θ (CompensatedMean.pack (Joint E (Blocks m F)) (pack a x) s 0)=
      outerSelected m M (fun i y => selectedInactiveCoupling m D d 0 [i.val] c θ
        (CompensatedMean.pack (Blocks m F) y s 0)) (pack a x) := by
  rw [outerInactiveCoupling,outerCoupling_inner_eq]
  simp only [outerSelected,selectedInactiveCoupling,outerFineSignal,zero_add,
    CompensatedMean.uProj_pack,CompensatedMean.sProj_pack,mul_sub,Finset.sum_sub_distrib,
    Finset.sum_mul,mul_assoc]

theorem outerInactiveCoupling_inner_support {m : ℕ} (M : Node E) (D : Geometry F) (d : ℕ)
    (hm : d < m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (r : ℕ → List ℕ → ℕ) (htree : TreeBlind D 0 d (by simpa using hm) W x r)
    (c θ s : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D d P).ell) (hwidth : ∀ P,(D d P).width=(D d []).width)
    (hz : ∀ P,∀ k : Fin ((D d P).n+1),r d P ≤ k.val →
      |(D d P).coordinates (x ⟨d,hm⟩) k|≤width c (D d []).width θ (levels θ)/8) :
    gradient (fun y => outerInactiveCoupling m M D d c θ
      (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) s 0)) x∈knownSpace W := by
  rw [funext (outerInactiveCoupling_inner_eq m M D d c θ s a)]
  apply outerSelected_inner_gradient_mem m M _
    (fun i => selectedInactiveCoupling_slice_contDiff m D d 0 [i.val] c θ s) a x (knownSpace W)
  intro i
  have hz' (t : ℕ) (ht : t=d) : ∀ P,∀ k : Fin ((D t P).n+1),r t P ≤ k.val →
      |(D t P).coordinates (x ⟨t,by omega⟩) k|≤width c (D t []).width θ (levels θ)/8 := by
    subst t
    exact hz
  exact selectedInactiveCoupling_tangent_support D d 0 [i.val] (by simpa using hm) W x r htree
    c θ s hc hcs hθ (by simpa only [zero_add] using hell) (by simpa only [zero_add] using hwidth)
    (hz' (0+d) (Nat.zero_add d))

theorem outerFineNormal_inner_eq (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (a : E) (x : Blocks m F) (q : ChiExtension.Normals s) :
    outerFineNormal m M D d c θ hc hβ hθ s i (pack (pack a x) q)=
      outerCoupling m M D d c θ (CompensatedMean.pack (Joint E (Blocks m F)) (pack a x) (q i) 0) := rfl

theorem outerInactiveNormal_inner_eq (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (hc : 0<c) (hβ : 0<(D d []).width) (hθ : 1≤θ) (s : ℕ) (i : Fin s)
    (a : E) (x : Blocks m F) (q : ChiExtension.Normals s) :
    outerInactiveNormal m M D d c θ hc hβ hθ s i (pack (pack a x) q)=
      outerInactiveCoupling m M D d c θ (CompensatedMean.pack (Joint E (Blocks m F)) (pack a x) (q i) 0) := by
  rw [outerInactiveNormal,outerFineNormal_inner_eq,outerSignalNormal,ChiExtension.normalTerm_formula]
  simp only [outerInactiveCoupling,CompensatedMean.uProj_pack,CompensatedMean.sProj_pack]

end Bilevel.ChiOuter
