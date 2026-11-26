import SampleReuse.IntegralDriftCharging
import SecondOrder.SignOrthogonality
import SecondOrder.FiniteCandidate

open MeasureTheory SecondOrder
open scoped InnerProductSpace Classical

namespace SampleReuse
noncomputable section

def SignPastEq {M : ℕ} (i : Fin M) (w w' : Fin M → Bool) : Prop :=
  ∀ j : Fin M, j < i → w j = w' j

def SignPredictable {E : Type*} {M : ℕ} (v : Fin M → (Fin M → Bool) → E) : Prop :=
  ∀ i w w', SignPastEq i w w' → v i w = v i w'

def SignStoppingTime {M : ℕ} (τ : (Fin M → Bool) → ℕ) : Prop :=
  ∀ i : Fin M, ∀ w w', SignPastEq i w w' → (τ w ≤ i.val ↔ τ w' ≤ i.val)

def predictableSignInnovation {E : Type*} [AddCommGroup E] [Module ℝ E] {M : ℕ}
    (v : Fin M → (Fin M → Bool) → E) (i : Fin M) (w : Fin M → Bool) : E :=
  signValue (w i) • v i w

theorem signPastEq_flip {M : ℕ} (i j : Fin M) (hij : i ≤ j) (w : Fin M → Bool) :
    SignPastEq i (flipSign j w) w := by
  intro k hk
  have hkj : k ≠ j := ne_of_lt (hk.trans_le hij)
  simp only [flipSign,Function.update_of_ne hkj]

theorem predictableSignInnovation_flip_self {E : Type*} [AddCommGroup E] [Module ℝ E] {M : ℕ}
    (v : Fin M → (Fin M → Bool) → E) (hv : SignPredictable v) (i : Fin M) (w : Fin M → Bool) :
    predictableSignInnovation v i (flipSign i w) = -predictableSignInnovation v i w := by
  unfold predictableSignInnovation
  rw [hv i _ _ (signPastEq_flip i i le_rfl w)]
  simp only [flipSign,Function.update_self,signValue_not,neg_smul]

theorem predictableSignInnovation_flip_later {E : Type*} [AddCommGroup E] [Module ℝ E] {M : ℕ}
    (v : Fin M → (Fin M → Bool) → E) (hv : SignPredictable v) (i j : Fin M) (hij : i < j)
    (w : Fin M → Bool) : predictableSignInnovation v i (flipSign j w) = predictableSignInnovation v i w := by
  unfold predictableSignInnovation
  rw [hv i _ _ (signPastEq_flip i j hij.le w)]
  simp only [flipSign,Function.update_of_ne hij.ne]

theorem predictableSignInnovation_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {M : ℕ} (v : Fin M → (Fin M → Bool) → E) (hv : SignPredictable v)
    (i j : Fin M) (hne : i ≠ j) :
    uniformMean (fun w => ⟪predictableSignInnovation v i w,predictableSignInnovation v j w⟫_ℝ) = 0 := by
  have hord (i j : Fin M) (hij : i < j) :
      uniformMean (fun w => ⟪predictableSignInnovation v i w,predictableSignInnovation v j w⟫_ℝ) = 0 := by
    have he := uniformMean_equiv (flipSignEquiv j)
      (fun w => ⟪predictableSignInnovation v i w,predictableSignInnovation v j w⟫_ℝ)
    change uniformMean (fun w => ⟪predictableSignInnovation v i (flipSign j w),
      predictableSignInnovation v j (flipSign j w)⟫_ℝ) = _ at he
    simp only [predictableSignInnovation_flip_later v hv i j hij,
      predictableSignInnovation_flip_self v hv,inner_neg_right] at he
    have hn : uniformMean (fun w => -⟪predictableSignInnovation v i w,predictableSignInnovation v j w⟫_ℝ) =
        -uniformMean (fun w => ⟪predictableSignInnovation v i w,predictableSignInnovation v j w⟫_ℝ) := by
      simp only [uniformMean,pmfMean,smul_neg,Finset.sum_neg_distrib]
    rw [hn] at he
    linarith
  rcases lt_or_gt_of_ne hne with hij | hij
  · exact hord i j hij
  · simpa only [real_inner_comm] using hord j i hij

theorem SignPredictable.stopped_interval {E : Type*} [Zero E] {M : ℕ}
    {v : Fin M → (Fin M → Bool) → E} (hv : SignPredictable v)
    (s t : (Fin M → Bool) → ℕ) (hs : SignStoppingTime s) (ht : SignStoppingTime t) :
    SignPredictable (fun i w => if s w ≤ i.val ∧ i.val < t w then v i w else 0) := by
  intro i w w' he
  have hmem : (s w ≤ i.val ∧ i.val < t w) ↔ (s w' ≤ i.val ∧ i.val < t w') :=
    and_congr (hs i w w' he) (by simpa only [not_le] using (ht i w w' he).not)
  simp only [hmem,hv i w w' he]

end
end SampleReuse
