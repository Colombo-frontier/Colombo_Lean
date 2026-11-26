import Bilevel.ChiCarrierClosedLocality
import Bilevel.ChiCarrierFineCouplingLocality

/-! Actual closed carriers after all ancestor selections. The future-child
condition is a concrete prefix-index statement; the needed flat release and
every joint derivative support fact are proved from it. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem selectedClosed_gradient_mem {m : ℕ} (D : Geometry E) (d t j : ℕ) (I : List ℕ)
    (hm : j+t+1 < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j (t+1) (by omega) W x r)
    (hhp : ∀ P,0<(D (j+t+1) P).parentWidth)
    (hw : ∀ P,(D (j+t+1) P).width≤(D (j+t+1) P).parentWidth)
    (hfuture : ∀ P,∀ i : Fin ((D (j+t) P).n+1),r (j+t) P ≤ i.val →
      r (j+t+1) (child P i.val)≤(D (j+t+1) (child P i.val)).n) :
    gradient (jointCarrier m D (d+1+t) j I t) x∈knownSpace W := by
  rw [jointCarrier_selectFamily]
  apply selectFamily_gradient_mem_of_blind D _
    (fun k P => jointCarrier_contDiff m D (d+1) k P 0 3) t j I (by omega) W x r
    (fun k P hk hkt => htree k P hk (by omega))
  intro P
  exact jointClosed_gradient_mem D d (j+t) P hm W x (r (j+t) P)
    (htree (j+t) P (by omega) (by omega))
    (fun i => r (j+t+1) (child P i.val))
    (fun i => htree (j+t+1) (child P i.val) (by omega) (by omega))
    (fun i => hhp (child P i.val)) (fun i => hw (child P i.val)) (hfuture P)

end Bilevel.ChiCarrier
