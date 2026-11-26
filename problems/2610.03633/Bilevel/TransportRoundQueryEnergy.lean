import Bilevel.TransportControllerRunQuery
import Bilevel.TransportRoundEnergy

/-! Actual raw-query events control the energy of the exact query-augmented
frozen generator store. The sequential analysis insertion and simultaneous
finite generator append have provably identical known spaces. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportRoundQuery
open EuclideanGaussian TransportNetwork TransportObserver ProjectionGeometry
set_option maxHeartbeats 800000

theorem queryPhaseKnown_le {n D : ℕ} (qs : List (Request n D)) (W V : Known n D)
    (hW : ∀ v,W v≤V v) (hq : ∀ q∈qs,q.2∈V q.1) : ∀ v,queryPhaseKnown qs W v≤V v := by
  induction qs generalizing W with
  | nil => exact hW
  | cons q qs ih =>
    apply ih (insert W q.1 q.2)
    · intro v
      by_cases hv : v=q.1
      · subst v
        rw [TransportNetwork.insert,Function.update_self]
        exact sup_le (hW q.1) (Submodule.span_le.mpr (by
          intro x hx
          have he : x=q.2 := Set.mem_singleton_iff.mp hx
          rw [he]
          exact hq q (List.mem_cons_self)))
      · rw [TransportNetwork.insert,Function.update_of_ne hv]
        exact hW v
    · intro q' hq'
      exact hq q' (List.mem_cons_of_mem q hq')

theorem queryPhaseKnown_mem {n D : ℕ} (qs : List (Request n D)) (W : Known n D)
    (q : Request n D) (hq : q∈qs) : q.2∈queryPhaseKnown qs W q.1 := by
  induction qs generalizing W with
  | nil => simp only [List.not_mem_nil] at hq
  | cons q' qs ih =>
    rcases List.mem_cons.mp hq with he | ht
    · subst q'
      apply queryPhaseKnown_mono qs (insert W q.1 q.2) q.1
      rw [TransportNetwork.insert,Function.update_self]
      exact (show Submodule.span ℝ {q.2}≤W q.1⊔Submodule.span ℝ {q.2} from le_sup_right)
        (Submodule.mem_span_singleton_self q.2)
    · exact ih (insert W q'.1 q'.2) ht

theorem queryPhase_energy {n D T : ℕ} (hT : T≤D) (a : ℝ) (qs : List (Request n D))
    (W : Known n D) (z : Latent n D) (I : Vertex n → Finset (Fin T))
    (hgood : ¬queryPhaseBad T hT a qs W z) :
    TransportRoundEnergy.total (queryPhaseKnown qs W) (frame T hT z) I ≤
      TransportRoundEnergy.total W (frame T hT z) I+(qs.length:ℝ)*a := by
  induction qs generalizing W with
  | nil => simp only [queryPhaseKnown,List.length_nil,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | cons q qs ih =>
    have hg := not_or.mp hgood
    have hhead : frameEnergy (W q.1⊔Submodule.span ℝ {q.2}) (frame T hT z q.1) Finset.univ-
        frameEnergy (W q.1) (frame T hT z q.1) Finset.univ≤a := le_of_not_gt hg.1
    have hsub : frameEnergy (W q.1⊔Submodule.span ℝ {q.2}) (frame T hT z q.1) (I q.1)-
        frameEnergy (W q.1) (frame T hT z q.1) (I q.1)≤a := by
      apply le_trans _ hhead
      simp only [TransportControllerQuery.raw_energy_increment]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have hh := TransportRoundEnergy.query_update W (frame T hT z) I q.1 q.2 hsub
    have ht := ih (insert W q.1 q.2) hg.2
    change TransportRoundEnergy.total (queryPhaseKnown qs (insert W q.1 q.2)) (frame T hT z) I≤_
    rw [List.length_cons,Nat.cast_add,Nat.cast_one]
    change TransportRoundEnergy.total (insert W q.1 q.2) (frame T hT z) I≤_ at hh
    linarith

end Bilevel.TransportRoundQuery

namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportRoundQuery TransportGeneratorStore
set_option maxHeartbeats 800000

theorem requests_mem {n D p : ℕ} (q : Queries n D p) (v : Vertex n) (i : Fin p) :
    (v,q v i)∈requests q := by
  apply List.mem_ofFn.mpr
  refine ⟨finProdFinEquiv (v,i),?_⟩
  simp only [Equiv.symm_apply_apply]

theorem requests_known {n D m p : ℕ} (g : Generators n D m) (q : Queries n D p) :
    queryPhaseKnown (requests q) (known g)=known (augment g q) := by
  funext v
  apply le_antisymm
  · apply queryPhaseKnown_le (requests q) (known g) (known (augment g q))
    · intro w
      rw [augment_span]
      exact le_sup_left
    · intro request hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      rw [augment_span]
      exact (show span (q (finProdFinEquiv.symm i).1)≤
        known g (finProdFinEquiv.symm i).1⊔span (q (finProdFinEquiv.symm i).1) from le_sup_right)
        (generator_mem _ (finProdFinEquiv.symm i).2)
  · rw [augment_span]
    apply sup_le (queryPhaseKnown_mono (requests q) (known g) v)
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact queryPhaseKnown_mem (requests q) (known g) (v,q v i) (requests_mem q v i)

theorem frozen_query_energy {n D m p T : ℕ} (hT : T≤D) (a : ℝ)
    (g : Generators n D m) (q : Queries n D p) (z : Latent n D) (I : Vertex n → Finset (Fin T))
    (hgood : ¬queryPhaseBad T hT a (requests q) (known g) z) :
    TransportRoundEnergy.total (known (augment g q)) (frame T hT z) I ≤
      TransportRoundEnergy.total (known g) (frame T hT z) I+(((n+1)*p:ℕ):ℝ)*a := by
  have hh := queryPhase_energy hT a (requests q) (known g) z I hgood
  rw [requests_known,requests_length] at hh
  exact hh

end Bilevel.TransportRound
