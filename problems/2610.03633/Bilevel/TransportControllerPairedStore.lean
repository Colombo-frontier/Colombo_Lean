import Bilevel.TransportControllerFreshStore
import Bilevel.TransportControllerOperator
import Bilevel.TransportControllerEdgeNetwork

/-! Finite Borel stores for the actual paired edge transcript. Fresh monitor
inputs are projected off the stored paired domain; their perpendicularity
and dimension bounds hold for every response, without a legality premise. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportControllerPairedStore
open EuclideanGaussian TransportGeneratorStore TransportEdgePosterior TransportRound
set_option maxHeartbeats 600000

abbrev State (D m : ℕ) := (Fin m → Space D) × (Fin m → Space D)

def pairs {D m : ℕ} (s : State D m) : Pairs D := List.ofFn (fun i => (s.1 i,s.2 i))

def insert {D m : ℕ} (s : State D m) (q y : Space D) : State D (m+1) :=
  (Fin.cons q s.1,Fin.cons y s.2)

theorem pairs_insert {D m : ℕ} (s : State D m) (q y : Space D) :
    pairs (insert s q y)=(q,y)::pairs s := by
  simp only [pairs,insert,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]

theorem domain_pairs {D m : ℕ} (s : State D m) : domain (pairs s)=span s.1 := by
  induction m with
  | zero => simp [pairs,domain,span,Set.range_eq_empty]
  | succ m ih =>
    have he : s=insert ((fun i : Fin m => s.1 i.succ),(fun i : Fin m => s.2 i.succ)) (s.1 0) (s.2 0) := by
      apply Prod.ext <;> funext i <;> cases i using Fin.cases <;> rfl
    rw [he,pairs_insert,domain,ih,insert,span_cons]

theorem range_pairs {D m : ℕ} (s : State D m) : range (pairs s)=span s.2 := by
  induction m with
  | zero => simp [pairs,range,span,Set.range_eq_empty]
  | succ m ih =>
    have he : s=insert ((fun i : Fin m => s.1 i.succ),(fun i : Fin m => s.2 i.succ)) (s.1 0) (s.2 0) := by
      apply Prod.ext <;> funext i <;> cases i using Fin.cases <;> rfl
    rw [he,pairs_insert,range,ih,insert,span_cons]

theorem pairs_supported {D m : ℕ} (s : State D m) (O : OrthogonalHaar.Group D) :
    Supports (pairs s) O ↔ ∀ i, O • s.1 i=s.2 i := by
  rw [TransportNetwork.supports_iff_pairs]
  constructor
  · intro h i
    exact h (s.1 i,s.2 i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro h p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact h i

theorem insert_measurable (D m : ℕ) :
    Measurable (fun p : State D m × Space D × Space D => insert p.1 p.2.1 p.2.2) := by
  apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro i <;> cases i using Fin.cases
  · exact measurable_fst.comp measurable_snd
  · rename_i i
    exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  · exact measurable_snd.comp measurable_snd
  · rename_i i
    exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)

def fresh {D m b : ℕ} (s : State D m) (v : Fin b → Space D) : Fin b → Space D :=
  residualFamily (projector D s.1) v

theorem fresh_span {D m b : ℕ} (s : State D m) (v : Fin b → Space D) :
    span (fresh s v)=residualSpace (domain (pairs s)) (span v) := by
  rw [fresh,projector_correct,residualFamily_span,domain_pairs]

theorem fresh_perp {D m b : ℕ} (s : State D m) (v : Fin b → Space D) :
    span (fresh s v)≤(domain (pairs s))ᗮ := by
  rw [fresh_span]
  exact residualSpace_perp _ _

theorem fresh_measurable (D m b : ℕ) :
    Measurable (fun p : State D m × (Fin b → Space D) => fresh p.1 p.2) :=
  (residualFamily_measurable D b).comp
    (((projector_measurable D m).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)

theorem fresh_angle_measurable {Ω : Type*} [MeasurableSpace Ω] {D m b w : ℕ}
    (s : Ω → State D m) (hs : Measurable s) (v : Ω → Fin b → Space D) (hv : Measurable v)
    (W : Ω → Fin w → Space D) (hW : Measurable W)
    (O : Ω → OrthogonalHaar.Group D) (hO : Measurable O) :
    MeasurableSet {ω | TransportControllerEdge.angleBad (span (W ω)) (span (fresh (s ω) (v ω))) (O ω)} := by
  apply TransportControllerOperator.angleBad_store_measurable D
  · have hh := (projector_measurable D w).comp hW
    simpa only [projector_correct] using hh
  · have hh := (projector_measurable D b).comp ((fresh_measurable D m b).comp (hs.prodMk hv))
    simpa only [projector_correct] using hh
  · exact hO

end Bilevel.TransportControllerPairedStore
