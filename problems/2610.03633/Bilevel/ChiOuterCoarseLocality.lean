import Bilevel.ChiCarrierDeepestLocality
import Bilevel.ChiSourceCoarseFamily

/-! Support of the exact source coarse family when the macro argument is
fixed, as it is in the partial conjugate inverse. The one-sided outer
selectors are the actual source weights; they introduce no inner direction. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtensionCalibration
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem outerSelected_inner_eq (m : ℕ) (M : Node E) (f : Fin (M.n+1) → Blocks m F → ℝ)
    (a : E) (x : Blocks m F) :
    outerSelected m M f (pack a x)=∑ i : Fin (M.n+1),wrappedSelector M i a*f i x := rfl

theorem outerSelected_inner_gradient_mem (m : ℕ) (M : Node E)
    (f : Fin (M.n+1) → Blocks m F → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (a : E) (x : Blocks m F) (W : Submodule ℝ (Blocks m F))
    (hm : ∀ i,gradient (f i) x∈W) : gradient (fun y => outerSelected m M f (pack a y)) x∈W := by
  change gradient (fun y => ∑ i : Fin (M.n+1),wrappedSelector M i a*f i y) x∈W
  apply gradient_sum_mem Finset.univ W _ (fun i => contDiff_const.mul (hf i))
  intro i _
  exact gradient_mul_mem W contDiff_const (hf i) x (gradient_const_mem W _ _) (hm i)

theorem outerDeepestA_inner_eq (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ)
    (a : E) (x : Blocks m F) :
    outerDeepestA m M D d (pack a x)=outerSelected m M (fun i => deepestCarrier m D d 0 [i.val]) (pack a x) := by
  simp only [outerDeepestA,outerCarrier,outerFineFrontier,outerSelected,deepestCarrier,mul_sub,Finset.sum_sub_distrib]

theorem outerDeepestA_inner_support {m : ℕ} (M : Node E) (D : Geometry F) (d : ℕ)
    (hm : d < m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (r : ℕ → List ℕ → ℕ) (htree : TreeBlind D 0 d (by simpa using hm) W x r) :
    gradient (fun y => outerDeepestA m M D d (pack a y)) x∈knownSpace W := by
  rw [show (fun y => outerDeepestA m M D d (pack a y))=
    (fun y => outerSelected m M (fun i => deepestCarrier m D d 0 [i.val]) (pack a y)) from
      funext (outerDeepestA_inner_eq m M D d a)]
  exact outerSelected_inner_gradient_mem m M _ (fun i => deepestCarrier_contDiff m D d 0 [i.val])
    a x (knownSpace W) (fun i => deepestCarrier_gradient_mem D d 0 [i.val] (by simpa using hm) W x r htree)

theorem outerCarrier_inner_support {m : ℕ} (M : Node E) (D : Geometry F) (J t : ℕ)
    (hm : J < m) (ht : t < J) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (r : ℕ → List ℕ → ℕ) (htree : TreeBlind D 0 J (by simpa using hm) W x r)
    (hhp : ∀ P,0<(D (t+1) P).parentWidth)
    (hw : ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
    (hfuture : ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
      r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n) :
    gradient (fun y => outerCarrier m M D J t (pack a y)) x∈knownSpace W := by
  apply outerSelected_inner_gradient_mem m M _ (fun i => jointCarrier_contDiff m D J 0 [i.val] t 3) a x
  intro i
  have hdepth : J-t-1+1+t=J := by omega
  rw [← hdepth]
  apply selectedClosed_gradient_mem D (J-t-1) t 0 [i.val] (by omega) W x r
  · intro k P hk hkt
    exact htree k P hk (by omega)
  · simpa only [zero_add] using hhp
  · simpa only [zero_add] using hw
  · intro P k hk
    simpa only [Nat.zero_add] using hfuture P ⟨k.val,by simpa only [Nat.zero_add] using k.isLt⟩
      (by simpa only [Nat.zero_add] using hk)

theorem coarseFamily_inner_support {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ)
    (hm : J < m) (a : E) (x : Blocks m F) (W : Fin m → Submodule ℝ F)
    (r : ℕ → List ℕ → ℕ) (htree : TreeBlind D 0 J (by simpa using hm) W x r)
    (hhp : ∀ t,t < J → ∀ P,0<(D (t+1) P).parentWidth)
    (hw : ∀ t,t < J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
    (hfuture : ∀ t,t < J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
      r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
    (i : Fin J) : gradient (fun y => coarseFamily m M D J i (pack a y)) x∈knownSpace W := by
  unfold coarseFamily
  by_cases hi : i.val+1=J
  · simp only [if_pos hi]
    exact outerDeepestA_inner_support M D J hm a x W r htree
  · simp only [if_neg hi]
    have hit : i.val+1 < J := by have := i.isLt;omega
    exact outerCarrier_inner_support M D J (i.val+1) hm hit a x W r htree
      (hhp _ hit) (hw _ hit) (hfuture _ hit)

end Bilevel.ChiOuter
