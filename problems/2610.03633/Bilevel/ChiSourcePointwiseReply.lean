import Bilevel.ChiSourceSeededEvents

/-! Pointwise source full-reply equality is lifted to the actual run. The
old store is the actual retained prefix; only the current successful coin
produces the incremented new store. Current-round outputs are never used
to choose that round's query vectors. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {Private S Q O Y : Type*} [MeasurableSpace Private] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

omit [MeasurableSpace Q] [MeasurableSpace O] in
theorem response_actual {counts : ℕ → ℕ} {J D : ℕ}
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (U : FiniteColumns counts J (Space D)) (q : Q) (n : ℕ) (coin : Bool) :
    (response counts J evaluate U (q,actual counts J n U) coin).1=
      evaluate q (actual counts J n U) (actual counts J (n+if coin then 1 else 0) U) coin := by
  change evaluate q (actual counts J n U)
    (ChiHierarchyIndex.update counts J (actual counts J n U) coin (revealReply counts J n coin U)) coin=_
  rw [update_actual]

omit [MeasurableSpace Private] in
theorem sourceGood_reply_from_energy {counts : ℕ → ℕ} {J D m : ℕ}
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (vectors : Fin m → Q → Space D) (hv : ∀ k,Measurable (vectors k))
    (output : FrameIndex counts J → Y → Space D) (ho : ∀ i,Measurable (output i))
    (initial : Private → S) (original : Orientations counts J D → Q → Bool → O) (cap : ℝ)
    (hreply : ∀ a n q coin,
      (∀ i : FrameIndex counts J,GenieProtocol.BoundedEnergy
        (sharedKnown counts J D n (columns hD a) (Submodule.span ℝ (Set.range (fun k => vectors k q))))
        (prefixSet (retained counts J n i)) (columns hD a i) cap) →
      original a q coin=evaluate q (actual counts J n (columns hD a))
        (actual counts J (n+if coin then 1 else 0) (columns hD a)) coin)
    (N : ℕ) (p : Sample (Orientations counts J D) Private Bool)
    (hgood : seedGood counts J D m hD A evaluate he (fun k z => vectors k z.1)
      (fun k => (hv k).comp measurable_fst) output ho initial N cap p)
    (t : ℕ) (ht : t<N) :
    let z := run counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 t
    original p.1 (A.query z.1) (p.2.2 t)=
      (response counts J evaluate (columns hD p.1) (A.query z.1,z.2) (p.2.2 t)).1 := by
  let z := run counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 t
  have hstore : z.2=actual counts J z.2.1 (columns hD p.1) :=
    run_store counts J A evaluate (columns hD p.1) (initial p.2.1) p.2.2 t
  have hE (i : FrameIndex counts J) := sourceGood_call counts J D m hD A evaluate he
    (fun k z => vectors k z.1) (fun k => (hv k).comp measurable_fst) output ho
    (fun c : Private × (ℕ → Bool) => initial c.1) Prod.snd N cap (p.2,p.1) hgood t ht i
  have hr := hreply p.1 z.2.1 (A.query z.1) (p.2.2 t) hE
  change original p.1 (A.query z.1) (p.2.2 t)=_
  rw [hr]
  conv_rhs => arg 1; arg 5; arg 2; rw [hstore]
  exact (response_actual evaluate (columns hD p.1) (A.query z.1) z.2.1 (p.2.2 t)).symm

end Bilevel.ChiHierarchyHaar
