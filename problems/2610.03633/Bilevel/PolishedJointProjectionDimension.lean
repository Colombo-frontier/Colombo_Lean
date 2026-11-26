import Bilevel.PolishedProjectionDimension
import Bilevel.ChiSourceObserverDimension

/-! The explicit logarithmic dimension bound for an auxiliary independent-frame
observer. This is an alternate prior: the polished two-level manuscript uses
one SM-column orthonormal micro frame. The failure union here charges the
columns of independent frames and is not that source-prior identification. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.PolishedJointProjectionDimension
open PolishedProjectionDimension ChiHierarchyHaar ChiHierarchyIndex
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

/-- The same logarithmic dimension expression, with two precoin raw
insertions per source query and one terminal insertion, controls all frame
observers simultaneously. No expanded compiler batch size occurs. -/
theorem joint_source_explicit_dimension {C : Type*} [MeasurableSpace C]
    (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k N reveal : ℕ} {H : Memory.{u}}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (L : ∀ i : FrameIndex counts J,OrdinaryFrame.Rules H D (chainSize i+1))
    (initial : ∀ _ : FrameIndex counts J,IndependentFrame.Context C D k → H)
    (hi : ∀ i,Measurable (initial i)) (t : ℕ) (R τ δ : ℝ)
    (hR : 0<R) (hτ : 0<τ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hreveal : reveal≤totalColumns counts J)
    (hd : sourceDimension (2*N+1) (totalColumns counts J) R τ δ≤D) :
    ∃ hD : ∀ i : FrameIndex counts J,chainSize i+1≤D,
      (ρ.prod (law counts J D)) {p | ∃ i : FrameIndex counts J,
        ¬OrdinaryFrame.Observed (L i) (τ^2/(4*R^2)) N reveal t
          (initial i (sourceExpose e hD i p).1,(⊥,∅)) (sourceExpose e hD i p).2}≤
      ENNReal.ofReal (δ/8) := by
  obtain ⟨n,b,hKD,hdim,hn,hb,hb2,hcap,henergy,hprob⟩ :=
    explicit_dimension_sufficient (2*N+1) (totalColumns counts J) D R τ δ
      (by omega) (totalColumns_pos counts J) hR hτ hδ hδ1 hd
  let hD : ∀ i : FrameIndex counts J,chainSize i+1≤D :=
    fun i => (chainSize_le_totalColumns counts J i).trans hKD
  have hdim' : (2*N+1)+reveal+(n+1)≤D := by omega
  have hcap' : (reveal:ℝ)*(((2*N+1:ℕ):ℝ)*b)≤1/2 := by
    have hle : (reveal:ℝ)≤totalColumns counts J := by exact_mod_cast hreveal
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans hcap
  refine ⟨hD,?_⟩
  exact (joint_observer_target ρ e hD L initial hi t b (τ^2/(4*R^2))
    hb hb2 hdim' hcap' henergy).trans_eq hprob

/-- A selected family may include only micro frames. Every other entire
frame remains independent frozen context in the sourceExpose experiment. -/
theorem selected_observer_target {C : Type*} [MeasurableSpace C]
    (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k N reveal n : ℕ} {H : Memory.{u}}
    {ι : Type*} [Fintype ι] (I : ι → FrameIndex counts J)
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (L : ∀ j : ι,OrdinaryFrame.Rules H D (chainSize (I j)+1))
    (initial : ∀ _ : ι,IndependentFrame.Context C D k → H)
    (hi : ∀ j,Measurable (initial j)) (t : ℕ) (b cap : ℝ)
    (hb : 0<b) (hb2 : b≤2) (hdim : (2*N+1)+reveal+(n+1)≤D)
    (hcap : (reveal:ℝ)*(((2*N+1:ℕ):ℝ)*b)≤1/2)
    (henergy : 2*((2*N+1:ℕ):ℝ)*b≤cap) :
    (ρ.prod (law counts J D)) {p | ∃ j : ι,
      ¬OrdinaryFrame.Observed (L j) cap N reveal t
        (initial j (sourceExpose e hD (I j) p).1,(⊥,∅)) (sourceExpose e hD (I j) p).2}≤
    ((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (∑ j : ι,(chainSize (I j)+1)) n b := by
  let B := fun j : ι => {p : C×Orientations counts J D |
    ¬OrdinaryFrame.Observed (L j) cap N reveal t
      (initial j (sourceExpose e hD (I j) p).1,(⊥,∅)) (sourceExpose e hD (I j) p).2}
  have he : {p | ∃ j : ι,¬OrdinaryFrame.Observed (L j) cap N reveal t
      (initial j (sourceExpose e hD (I j) p).1,(⊥,∅)) (sourceExpose e hD (I j) p).2}=⋃ j,B j := by
    ext p
    simp only [Set.mem_iUnion,Set.mem_setOf_eq,B]
  rw [he]
  calc
    _ ≤ ∑' j,(ρ.prod (law counts J D)) (B j) := measure_iUnion_le _
    _ = ∑ j,(ρ.prod (law counts J D)) (B j) := tsum_fintype _
    _ ≤ ∑ j,((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (chainSize (I j)+1) n b := by
      apply Finset.sum_le_sum
      intro j _
      have hh := source_observer ρ e hD (I j) (L j) (initial j) (hi j) t b hb hb2 hdim hcap
      refine (measure_mono ?_).trans hh
      intro p hp hsafe
      exact hp (OrdinaryFrame.observed_mono (L j) henergy N reveal t _ _ hsafe)
    _ = _ := by rw [←Finset.mul_sum,sum_failurePerQuery]

/-- Sharp total-column charge S*M for S independent M-column auxiliary frames.
Only within-frame orthonormality is used by the Haar observer. -/
theorem micro_source_explicit_dimension {C : Type*} [MeasurableSpace C]
    (ρ : Measure C) [IsProbabilityMeasure ρ]
    {counts : ℕ → ℕ} {J D k N reveal S M : ℕ} {H : Memory.{u}}
    (I : Fin S → FrameIndex counts J)
    (hsize : ∀ j,chainSize (I j)+1=M)
    (hall : ∀ i : FrameIndex counts J,chainSize i+1≤S*M)
    (e : FrameIndex counts J ≃ Fin (k+1))
    (L : ∀ j : Fin S,OrdinaryFrame.Rules H D (chainSize (I j)+1))
    (initial : ∀ _ : Fin S,IndependentFrame.Context C D k → H)
    (hi : ∀ j,Measurable (initial j)) (t : ℕ) (R τ δ : ℝ)
    (hS : 0<S) (hM : 0<M) (hR : 0<R) (hτ : 0<τ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hreveal : reveal≤S*M) (hd : sourceDimension (2*N+1) (S*M) R τ δ≤D) :
    ∃ hD : ∀ i : FrameIndex counts J,chainSize i+1≤D,
      (ρ.prod (law counts J D)) {p | ∃ j : Fin S,
        ¬OrdinaryFrame.Observed (L j) (τ^2/(4*R^2)) N reveal t
          (initial j (sourceExpose e hD (I j) p).1,(⊥,∅)) (sourceExpose e hD (I j) p).2}≤
      ENNReal.ofReal (δ/8) := by
  obtain ⟨n,b,hKD,hdim,hn,hb,hb2,hcap,henergy,hprob⟩ :=
    explicit_dimension_sufficient (2*N+1) (S*M) D R τ δ
      (by omega) (Nat.mul_pos hS hM) hR hτ hδ hδ1 hd
  let hD : ∀ i : FrameIndex counts J,chainSize i+1≤D := fun i => (hall i).trans hKD
  have hdim' : (2*N+1)+reveal+(n+1)≤D := by omega
  have hcap' : (reveal:ℝ)*(((2*N+1:ℕ):ℝ)*b)≤1/2 := by
    have hle : (reveal:ℝ)≤(S*M:ℕ) := by exact_mod_cast hreveal
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans hcap
  have hsum : (∑ j : Fin S,(chainSize (I j)+1))=S*M := by simp only [hsize,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  refine ⟨hD,?_⟩
  have hh := selected_observer_target ρ I e hD L initial hi t b (τ^2/(4*R^2))
    hb hb2 hdim' hcap' henergy
  rw [hsum] at hh
  exact hh.trans_eq hprob

end Bilevel.PolishedJointProjectionDimension
