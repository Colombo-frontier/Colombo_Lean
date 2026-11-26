import SecondOrder.MartingaleEnergy
import SecondOrder.ReindexEnergy

open MeasureTheory Filter
open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section

def selectedMartingaleIncrement {Ω E R : Type*} [Zero E] {M : ℕ}
    (m : Fin M → Ω → E) (label : Fin M → Ω → R) (r : R) (i : Fin M) (w : Ω) : E :=
  if label i w=r then m i w else 0

def reindexedMartingale {Ω E R : Type*} [AddCommMonoid E] {M : ℕ}
    (m : Fin M → Ω → E) (label : Fin M → Ω → R) (r : R) (w : Ω) : E :=
  ∑ i, selectedMartingaleIncrement m label r i w

variable {Ω E R : Type*} {m₀ : MeasurableSpace Ω} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ] {M : ℕ}

theorem selectedMartingaleIncrement_memLp (m : Fin M → Ω → E) (label : Fin M → Ω → R)
    (r : R) (i : Fin M) (hl : MeasurableSet {w | label i w=r}) (hm : MemLp (m i) 2 μ) :
    MemLp (selectedMartingaleIncrement m label r i) 2 μ := by
  simpa only [selectedMartingaleIncrement,Set.indicator,Set.mem_setOf_eq] using MemLp.indicator hl hm

/-- Predictable selection preserves orthogonality for arbitrary L2
martingale differences, including nonsymmetric and non-discrete laws. -/
theorem selectedMartingale_cross_lt (m : Fin M → Ω → E) (label : Fin M → Ω → R)
    (past : Fin M → MeasurableSpace Ω) (hp : ∀ j, past j≤m₀)
    (hmono : Monotone past) (hm : ∀ i, MemLp (m i) 2 μ)
    (hadapt : ∀ i j, i<j → AEStronglyMeasurable[past j] (m i) μ)
    (hzero : ∀ j, μ[m j | past j]=ᵐ[μ] (fun _ => 0))
    (hl : ∀ r i, MeasurableSet[past i] {w | label i w=r})
    (r s : R) (i j : Fin M) (hij : i<j) :
    (∫ w, ⟪selectedMartingaleIncrement m label r i w,
      selectedMartingaleIncrement m label s j w⟫_ℝ ∂μ)=0 := by
  let B : Set Ω := {w | label i w=r} ∩ {w | label j w=s}
  have hB : MeasurableSet[past j] B := (hmono hij.le _ (hl r i)).inter (hl s j)
  have hBm : MeasurableSet B := hp j _ hB
  have hXi : MemLp (B.indicator (m i)) 2 μ := MemLp.indicator hBm (hm i)
  have hXm : AEStronglyMeasurable[past j] (B.indicator (m i)) μ := by
    obtain ⟨g,hg,he⟩ := hadapt i j hij
    refine ⟨B.indicator g,hg.indicator hB,?_⟩
    filter_upwards [he] with w hw
    simp only [Set.indicator]
    split_ifs <;> simp [hw]
  have hh := integral_inner_zero_of_condExp (μ := μ) (X := B.indicator (m i)) (Y := m j)
    (s := past j) (hp j) hXi (hm j) hXm (hzero j)
  apply Eq.trans _ hh
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [selectedMartingaleIncrement,Set.indicator,B,Set.mem_inter_iff,Set.mem_setOf_eq]
  by_cases hr : label i w=r <;> by_cases hs : label j w=s <;> simp [hr,hs]

theorem reindexedMartingale_moments (m : Fin M → Ω → E) (label : Fin M → Ω → R)
    (r : R) (hl : ∀ i, MeasurableSet {w | label i w=r}) (hm : ∀ i, MemLp (m i) 2 μ) :
    Integrable (reindexedMartingale m label r) μ ∧
      Integrable (fun w => ‖reindexedMartingale m label r w‖^2) μ := by
  have hx (i : Fin M) := selectedMartingaleIncrement_memLp m label r i (hl i) (hm i)
  have hx1 (i : Fin M) := (hx i).integrable (show (1:ENNReal)≤2 by norm_num)
  have hx2 (i : Fin M) := (memLp_two_iff_integrable_sq_norm (hx i).1).mp (hx i)
  exact ⟨integrable_finset_sum _ (fun i _ => hx1 i),
    integrable_norm_sum_sq _ _ (fun i _ => hx1 i) (fun i _ => hx2 i)⟩

/-- Distinct predictable labels give orthogonal reindexed increments. No
independence, sign symmetry or deterministic epoch boundaries are assumed. -/
theorem reindexedMartingale_orthogonal (m : Fin M → Ω → E) (label : Fin M → Ω → R)
    (past : Fin M → MeasurableSpace Ω) (hp : ∀ j, past j≤m₀)
    (hmono : Monotone past) (hm : ∀ i, MemLp (m i) 2 μ)
    (hadapt : ∀ i j, i<j → AEStronglyMeasurable[past j] (m i) μ)
    (hzero : ∀ j, μ[m j | past j]=ᵐ[μ] (fun _ => 0))
    (hl : ∀ r i, MeasurableSet[past i] {w | label i w=r})
    (r s : R) (hrs : r≠s) :
    (∫ w, ⟪reindexedMartingale m label r w,reindexedMartingale m label s w⟫_ℝ ∂μ)=0 := by
  have hx (r : R) (i : Fin M) := selectedMartingaleIncrement_memLp m label r i (hp i _ (hl r i)) (hm i)
  have hx1 (r : R) (i : Fin M) := (hx r i).integrable (show (1:ENNReal)≤2 by norm_num)
  have hx2 (r : R) (i : Fin M) := (memLp_two_iff_integrable_sq_norm (hx r i).1).mp (hx r i)
  have hc (i j : Fin M) := integrable_inner_of_second_moments
    (hx1 r i) (hx1 s j) (hx2 r i) (hx2 s j)
  simp only [reindexedMartingale]
  simp_rw [sum_inner,inner_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hc i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finset_sum _ (fun j _ => hc i j)]
  apply Finset.sum_eq_zero
  intro j _
  rcases lt_trichotomy i j with hij | hij | hij
  · exact selectedMartingale_cross_lt m label past hp hmono hm hadapt hzero hl r s i j hij
  · subst j
    have hz (w : Ω) : ⟪selectedMartingaleIncrement m label r i w,
        selectedMartingaleIncrement m label s i w⟫_ℝ=0 := by
      unfold selectedMartingaleIncrement
      split_ifs with hr hs hs <;> simp_all
    simp_rw [hz]
    simp
  · simpa only [real_inner_comm] using
      selectedMartingale_cross_lt m label past hp hmono hm hadapt hzero hl s r j i hij

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem reindexedMartingale_energy (m : Fin M → Ω → E) (label : Fin M → Ω → R)
    (hinj : ∀ w, Function.Injective (fun i => label i w)) (s : Finset R)
    (hs : ∀ w i, label i w∈s) (w : Ω) :
    (∑ r ∈ s, ‖reindexedMartingale m label r w‖^2)=∑ i, ‖m i w‖^2 :=
  sum_injective_fiber_energy (fun i => label i w) (hinj w) (fun i => m i w) s (hs w)

end
end SecondOrder
