import Bilevel.PrefixFrameStore
import Bilevel.SourceFrameBatchPreEnergy

/-! A deterministic public release schedule and an actual finite auxiliary
prefix store. Each round reveals at most one column of each frame. All
updates use only the supplied newly disclosed vectors. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian ChiPrefixEvaluation
set_option autoImplicit false

structure Schedule (k T : ℕ) where
  count : ℕ → Fin k → ℕ
  zero : ∀ i, count 0 i = 0
  mono : ∀ t i, count t i ≤ count (t+1) i
  step : ∀ t i, count (t+1) i ≤ count t i+1
  bound : ∀ t i, count t i ≤ T+1

abbrev Columns (k T D : ℕ) := Fin k → Fin (T+1) → Space D
abbrev Store (k T D : ℕ) := Fin k → PrefixStore T (Space D)

def initialStore (k T D : ℕ) : Store k T D := fun _ => ChiPrefixEvaluation.initialStore T

def actualStore {k T D : ℕ} (P : Schedule k T) (t : ℕ) (U : Columns k T D) : Store k T D :=
  fun i => ChiPrefixEvaluation.actualStore T (P.count t i) (U i)

def request {k T : ℕ} (P : Schedule k T) (t : ℕ) (i : Fin k) : Bool :=
  decide (P.count t i < P.count (t+1) i)

def column {k T : ℕ} (P : Schedule k T) (t : ℕ) (i : Fin k) : Fin (T+1) :=
  if h : P.count t i < T+1 then ⟨P.count t i,h⟩ else 0

def replies {k T D : ℕ} (P : Schedule k T) (t : ℕ) (U : Columns k T D) : Fin k → Space D :=
  fun i => if request P t i then U i (column P t i) else 0

def advance {k T D : ℕ} (P : Schedule k T) (t : ℕ)
    (s : Store k T D) (y : Fin k → Space D) : Store k T D :=
  fun i => advanceStore T (s i) (P.count (t+1) i) (y i)

theorem advance_measurable {k T D : ℕ} (P : Schedule k T) (t : ℕ) :
    Measurable (fun z : Store k T D × (Fin k → Space D) => advance P t z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  have hm : Measurable (fun z : Store k T D × (Fin k → Space D) =>
      (z.1 i,(P.count (t+1) i,z.2 i))) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (advanceStore_measurable T).comp hm

theorem actualStore_zero {k T D : ℕ} (P : Schedule k T) (U : Columns k T D) :
    actualStore P 0 U = initialStore k T D := by
  funext i
  simp only [actualStore,initialStore,P.zero,ChiPrefixEvaluation.actualStore_zero]

theorem advance_actualStore {k T D : ℕ} (P : Schedule k T) (t : ℕ) (U : Columns k T D) :
    advance P t (actualStore P t U) (replies P t U) = actualStore P (t+1) U := by
  funext i
  by_cases h : P.count t i < P.count (t+1) i
  · have hb : P.count t i < T+1 := lt_of_lt_of_le h (P.bound (t+1) i)
    simpa only [advance,actualStore,replies,request,decide_eq_true_eq,if_pos h,
      column,dif_pos hb,actualNextColumn] using
      ChiPrefixEvaluation.advance_actualStore T (P.count t i) (P.count (t+1) i)
        (U i) (P.mono t i) (P.step t i) (P.bound (t+1) i)
  · have he : P.count (t+1) i = P.count t i := le_antisymm (le_of_not_gt h) (P.mono t i)
    simp only [advance,actualStore,replies,request,decide_eq_true_eq,if_neg h,he,
      advanceStore,ChiPrefixEvaluation.actualStore,lt_self_iff_false,if_false]

end Bilevel.TransportAuxiliaryFrame
