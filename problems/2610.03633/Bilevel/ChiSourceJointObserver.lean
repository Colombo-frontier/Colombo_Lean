import Bilevel.ChiSourceCallProbability
import Bilevel.SourceObserverBudget

/-! A simultaneous finite-frame observer on the one original source prior.
The union bound charges the total number of frame columns, including the
macro frame. Every constituent event concerns the actual compiled run. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex EuclideanGaussian ProjectionPosterior TransportControllerMachine

def totalColumns (counts : ℕ → ℕ) (J : ℕ) : ℕ := ∑ i : FrameIndex counts J, (chainSize i+1)

theorem chainSize_le_totalColumns (counts : ℕ → ℕ) (J : ℕ) (i : FrameIndex counts J) :
    chainSize i+1≤totalColumns counts J := by
  exact Finset.single_le_sum (f:=fun j : FrameIndex counts J => chainSize j+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem totalColumns_pos (counts : ℕ → ℕ) (J : ℕ) : 0<totalColumns counts J :=
  (Nat.zero_lt_succ _).trans_le (chainSize_le_totalColumns counts J (Sum.inl ()))

theorem sum_failurePerQuery {ι : Type*} [Fintype ι] (T : ι → ℕ) (r : ℕ) (b : ℝ) :
    ∑ i, GenieProtocol.failurePerQuery (T i) r b=GenieProtocol.failurePerQuery (∑ i,T i) r b := by
  unfold GenieProtocol.failurePerQuery
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [←Finset.sum_mul,Nat.cast_sum]

theorem joint_observer_failure {C : Type*} [MeasurableSpace C] (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k N R r : ℕ} {H : Memory.{u}}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (L : ∀ i : FrameIndex counts J,OrdinaryFrame.Rules H D (chainSize i+1))
    (initial : ∀ _ : FrameIndex counts J,IndependentFrame.Context C D k → H)
    (hi : ∀ i,Measurable (initial i))
    (t : ℕ) (b : ℝ) (hb : 0<b) (hb2 : b≤2) (hdim : (2*N+1)+R+(r+1)≤D)
    (hcap : (R:ℝ)*(((2*N+1:ℕ):ℝ)*b)≤1/2) :
    (ρ.prod (law counts J D)) {p | ∃ i : FrameIndex counts J,
      ¬OrdinaryFrame.Observed (L i) (2*((2*N+1:ℕ):ℝ)*b) N R t
        (initial i (sourceExpose e hD i p).1,(⊥,∅)) (sourceExpose e hD i p).2} ≤
      ((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (totalColumns counts J) r b := by
  let B := fun i : FrameIndex counts J => {p : C × Orientations counts J D |
    ¬OrdinaryFrame.Observed (L i) (2*((2*N+1:ℕ):ℝ)*b) N R t
      (initial i (sourceExpose e hD i p).1,(⊥,∅)) (sourceExpose e hD i p).2}
  have he : {p | ∃ i : FrameIndex counts J,
      ¬OrdinaryFrame.Observed (L i) (2*((2*N+1:ℕ):ℝ)*b) N R t
        (initial i (sourceExpose e hD i p).1,(⊥,∅)) (sourceExpose e hD i p).2} = ⋃ i,B i := by
    ext p
    simp only [B,Set.mem_iUnion,Set.mem_setOf_eq]
  rw [he]
  calc
    (ρ.prod (law counts J D)) (⋃ i,B i) ≤ ∑' i,(ρ.prod (law counts J D)) (B i) := measure_iUnion_le _
    _ = ∑ i,(ρ.prod (law counts J D)) (B i) := tsum_fintype _
    _ ≤ ∑ i,((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (chainSize i+1) r b := by
      apply Finset.sum_le_sum
      intro i _
      exact source_observer ρ e hD i (L i) (initial i) (hi i) t b hb hb2 hdim hcap
    _ = ((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (totalColumns counts J) r b := by
      rw [←Finset.mul_sum,sum_failurePerQuery]
      rfl

theorem joint_observed_measurable {C : Type*} [MeasurableSpace C] {counts : ℕ → ℕ} {J D k : ℕ}
    {H : Memory.{u}} (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (L : ∀ i : FrameIndex counts J,OrdinaryFrame.Rules H D (chainSize i+1))
    (initial : ∀ _ : FrameIndex counts J,IndependentFrame.Context C D k → H)
    (hi : ∀ i,Measurable (initial i)) (N R t : ℕ) (cap : ℝ) :
    MeasurableSet {p : C × Orientations counts J D | ∀ i : FrameIndex counts J,
      OrdinaryFrame.Observed (L i) cap N R t
        (initial i (sourceExpose e hD i p).1,(⊥,∅)) (sourceExpose e hD i p).2} := by
  convert MeasurableSet.iInter (fun i : FrameIndex counts J =>
    source_observed_measurable e hD i (L i) (initial i) (hi i) N R t cap) using 1
  ext p
  simp only [Set.mem_iInter,Set.mem_setOf_eq]

end Bilevel.ChiHierarchyHaar
