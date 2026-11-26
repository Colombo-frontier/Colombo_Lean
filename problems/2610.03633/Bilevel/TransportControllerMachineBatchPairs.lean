import Bilevel.TransportControllerMachineBatch

/-! Exact physical domains and ranges after the concrete frozen batch.
These identities retain the entering paired history and account for every
real response; they are used to identify the actual fresh monitor domain. -/
noncomputable section
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportGeneratorStore TransportEdgePosterior
set_option maxHeartbeats 600000

theorem tuple_cons {D b : ℕ} (v : Fin (b+1) → Space D) : v=Fin.cons (v 0) (fun i => v i.succ) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem insertMany_domain {D b m : ℕ} (rev : Bool) (s : TransportControllerPairedStore.State D m)
    (q y : Fin b → Space D) :
    domain (TransportControllerPairedStore.pairs (insertMany rev s q y))=
      domain (TransportControllerPairedStore.pairs s)⊔span (if rev then y else q) := by
  induction b generalizing m with
  | zero => simp [insertMany,span,Set.range_eq_empty]
  | succ b ih =>
    cases rev with
    | false =>
      simp only [insertMany,Bool.false_eq_true,ite_false,ih,TransportControllerPairedStore.pairs_insert,domain]
      conv_rhs => rw [tuple_cons q,span_cons]
      simp only [sup_assoc,sup_comm,sup_left_comm]
    | true =>
      simp only [insertMany,ite_true,ih,TransportControllerPairedStore.pairs_insert,domain]
      conv_rhs => rw [tuple_cons y,span_cons]
      simp only [sup_assoc,sup_comm,sup_left_comm]

theorem insertMany_range {D b m : ℕ} (rev : Bool) (s : TransportControllerPairedStore.State D m)
    (q y : Fin b → Space D) :
    range (TransportControllerPairedStore.pairs (insertMany rev s q y))=
      range (TransportControllerPairedStore.pairs s)⊔span (if rev then q else y) := by
  induction b generalizing m with
  | zero => simp [insertMany,span,Set.range_eq_empty]
  | succ b ih =>
    cases rev with
    | false =>
      simp only [insertMany,Bool.false_eq_true,ite_false,ih,TransportControllerPairedStore.pairs_insert,range]
      conv_rhs => rw [tuple_cons y,span_cons]
      simp only [sup_assoc,sup_comm,sup_left_comm]
    | true =>
      simp only [insertMany,ite_true,ih,TransportControllerPairedStore.pairs_insert,range]
      conv_rhs => rw [tuple_cons q,span_cons]
      simp only [sup_assoc,sup_comm,sup_left_comm]

theorem batchResponse_span {D b : ℕ} (rev : Bool) (q : Fin b → Space D) (O : OrthogonalHaar.Group D) :
    span (batchResponse rev q O)=(span q).map (isometry D (if rev then O⁻¹ else O)).toLinearEquiv.toLinearMap := by
  cases rev <;> exact transported_span q _

theorem insertMany_support {D b m : ℕ} (rev : Bool) (s : TransportControllerPairedStore.State D m)
    (q : Fin b → Space D) (O : OrthogonalHaar.Group D)
    (hs : Supports (TransportControllerPairedStore.pairs s) O) :
    Supports (TransportControllerPairedStore.pairs (insertMany rev s q (batchResponse rev q O))) O := by
  induction b generalizing m with
  | zero => exact hs
  | succ b ih =>
    cases rev with
    | false =>
      apply ih
      simp only [Bool.false_eq_true,ite_false]
      rw [TransportControllerPairedStore.pairs_insert]
      exact ⟨rfl,hs⟩
    | true =>
      apply ih
      simp only [ite_true]
      rw [TransportControllerPairedStore.pairs_insert]
      refine ⟨?_,hs⟩
      change O • (O⁻¹ • q 0)=q 0
      exact smul_inv_smul O (q 0)

end Bilevel.TransportControllerMachine
