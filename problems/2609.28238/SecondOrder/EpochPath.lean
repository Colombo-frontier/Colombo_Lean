import SecondOrder.PhysicalPrefix
import SecondOrder.EpochIntervals

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem sum_injective_fiber_at {I R E : Type*} [Fintype I] [AddCommMonoid E]
    (label : I → R) (hl : Function.Injective label) (x : I → E) (i : I) :
    (∑ j, if label j=label i then x j else 0) = x i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [show label j ≠ label i from fun hh => hji (hl hh)]
  · simp

def idealEpochBegin {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (e : ℕ) : ℕ :=
  epochBoundary (idealPhysicalLength L s policy w) q (idealGradientFlag L s policy (extendSigns w)) e

def idealEpochLength {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (e : ℕ) : ℕ :=
  epochLength (idealPhysicalLength L s policy w) q (idealGradientFlag L s policy (extendSigns w)) e

/-- The actual shifted epoch path, frozen at its last physical endpoint. -/
def idealEpochPath {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (e k : ℕ) : Point d :=
  (idealPath L s policy (extendSigns w) (idealEpochBegin q L s policy w e+min k (idealEpochLength q L s policy w e))).point

theorem idealEpochLength_le {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (e : ℕ) : idealEpochLength q L s policy w e ≤ M :=
  (epochLength_le_cap _ _ _ _).trans (idealPhysicalLength_le L s policy w)

theorem sum_idealEpochLength {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) : (∑ e : Fin M, idealEpochLength q L s policy w e.val) = idealPhysicalLength L s policy w :=
  sum_epochLength (idealPhysicalLength_le L s policy w) q _

theorem idealEpochPath_endpoint {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (e k : ℕ) (hk : k ≤ idealEpochLength q L s policy w e) :
    idealEpochPath q L s policy w e k =
      (idealPath L s policy (extendSigns w) (idealEpochBegin q L s policy w e+k)).point := by
  simp only [idealEpochPath,min_eq_left hk]

theorem idealEpochIncrement_eq_sum {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) (r : ℕ × ℕ) :
    idealEpochDrift q L s policy r w+idealEpochInnovation q L s policy r w =
      ∑ i : Fin M, if epochAddress q (idealGradientFlag L s (policy w.1) (extendSigns w.2)) i.val = r then
        (idealPath L s (policy w.1) (extendSigns w.2) (i.val+1)).point-
          (idealPath L s (policy w.1) (extendSigns w.2) i.val).point else 0 := by
  rw [idealEpochDrift_eq hq,idealEpochInnovation_eq hq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · exact (mixedIdeal_displacement L s policy w i).symm
  · simp

theorem idealEpochIncrement_active {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) (e k : ℕ)
    (hk : k < idealEpochLength q L s (policy w.1) w.2 e) :
    idealEpochDrift q L s policy (e,k) w+idealEpochInnovation q L s policy (e,k) w =
      (idealPath L s (policy w.1) (extendSigns w.2) (idealEpochBegin q L s (policy w.1) w.2 e+k+1)).point-
        (idealPath L s (policy w.1) (extendSigns w.2) (idealEpochBegin q L s (policy w.1) w.2 e+k)).point := by
  let g := idealGradientFlag L s (policy w.1) (extendSigns w.2)
  let N := idealPhysicalLength L s (policy w.1) w.2
  have ht := (epoch_local_time (show k < epochLength N q g e from hk)).1
  let i : Fin M := ⟨epochBoundary N q g e+k,ht.trans_le (idealPhysicalLength_le L s (policy w.1) w.2)⟩
  have hl : epochAddress q g i.val = (e,k) := epoch_local_address hq hk
  rw [idealEpochIncrement_eq_sum hq]
  have hh := sum_injective_fiber_at (fun i : Fin M => epochAddress q g i.val)
    ((epochAddress_injective hq g).comp Fin.val_injective)
    (fun i : Fin M => (idealPath L s (policy w.1) (extendSigns w.2) (i.val+1)).point-
      (idealPath L s (policy w.1) (extendSigns w.2) i.val).point) i
  rw [hl] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> rfl

theorem idealEpochIncrement_inactive {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) (e k : ℕ)
    (hk : idealEpochLength q L s (policy w.1) w.2 e ≤ k) :
    idealEpochDrift q L s policy (e,k) w+idealEpochInnovation q L s policy (e,k) w = 0 := by
  rw [idealEpochIncrement_eq_sum hq]
  apply Finset.sum_eq_zero
  intro i hi
  let g := idealGradientFlag L s (policy w.1) (extendSigns w.2)
  let N := idealPhysicalLength L s (policy w.1) w.2
  by_cases he : epochAddress q g i.val = (e,k)
  · rw [if_pos he]
    have hn : N ≤ i.val := by
      by_contra hh
      have ht : i.val < N := Nat.lt_of_not_ge hh
      have hf : epochOfStep q g i.val = e := congrArg Prod.fst he
      have hl : i.val-(epochClock q g i.val).start = k := congrArg Prod.snd he
      have hb := epochBoundary_eq_clock hq ht hf
      have hi' := (epoch_interval_iff N q g e i.val).mpr ⟨ht,hf⟩
      change epochLength N q g e ≤ k at hk
      dsimp only [epochLength] at hk
      omega
    have hp : stateMoves (idealPath L s (policy w.1) (extendSigns w.2) M) ≤ i.val := by
      simpa only [idealPath_extendSigns] using hn
    have hz := idealPath_increments_after_length L s (policy w.1) (extendSigns w.2) i.isLt hp
    rw [idealPath_displacement,hz.1,hz.2,zero_add]
  · exact if_neg he

/-- The reindexed drift plus innovation is exactly every increment of the
actual epoch path, with zero padding after its physical end. -/
theorem idealEpochPath_displacement {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) (e k : ℕ) :
    idealEpochPath q L s (policy w.1) w.2 e (k+1)-idealEpochPath q L s (policy w.1) w.2 e k =
      idealEpochDrift q L s policy (e,k) w+idealEpochInnovation q L s policy (e,k) w := by
  by_cases hk : k < idealEpochLength q L s (policy w.1) w.2 e
  · rw [idealEpochPath_endpoint _ _ _ _ _ _ _ (by omega),idealEpochPath_endpoint _ _ _ _ _ _ _ hk.le]
    simpa only [Nat.add_assoc] using (idealEpochIncrement_active hq L s policy w e k hk).symm
  · have hk' : idealEpochLength q L s (policy w.1) w.2 e ≤ k := Nat.le_of_not_gt hk
    rw [idealEpochIncrement_inactive hq L s policy w e k hk']
    simp [idealEpochPath,min_eq_right hk',min_eq_right (hk'.trans (Nat.le_succ k))]

end
end SecondOrder
