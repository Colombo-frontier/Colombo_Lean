import SecondOrder.MixedSigns

open MeasureTheory
open scoped Classical BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

theorem signedInnovation_cross_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {M : ℕ}
    (v u : (i : Fin M) → (Fin i.val → Bool) → E) (i j : Fin M) (hij : i ≠ j) :
    uniformMean (fun w => ⟪signedInnovation v i w,signedInnovation u j w⟫_ℝ) = 0 := by
  have hh := signedInnovation_orthogonal (fun k past => if k=i then v k past else u k past) i j hij
  simpa only [signedInnovation,if_pos rfl,if_neg hij.symm] using hh

variable {Ξ E R : Type*} [MeasurableSpace Ξ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {η : Measure Ξ} [IsProbabilityMeasure η] {M : ℕ}

theorem mixedInnovation_cross_orthogonal
    (v u : Ξ → (i : Fin M) → (Fin i.val → Bool) → E) (i j : Fin M) (hij : i ≠ j)
    (hvi : Integrable (mixedInnovation v i) (η.prod (signLaw M)))
    (huj : Integrable (mixedInnovation u j) (η.prod (signLaw M)))
    (hvi2 : Integrable (fun w => ‖mixedInnovation v i w‖^2) (η.prod (signLaw M)))
    (huj2 : Integrable (fun w => ‖mixedInnovation u j w‖^2) (η.prod (signLaw M))) :
    (∫ w, ⟪mixedInnovation v i w,mixedInnovation u j w⟫_ℝ ∂η.prod (signLaw M)) = 0 := by
  rw [integral_prod _ (integrable_inner_of_second_moments hvi huj hvi2 huj2)]
  have he (ξ : Ξ) : (∫ w, ⟪mixedInnovation v i (ξ,w),mixedInnovation u j (ξ,w)⟫_ℝ ∂signLaw M) = 0 := by
    rw [integral_signLaw]
    exact signedInnovation_cross_orthogonal (v ξ) (u ξ) i j hij
  simp_rw [he]
  simp

def selectedDirection (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R) (r : R)
    (ξ : Ξ) (i : Fin M) (past : Fin i.val → Bool) : E :=
  if label ξ i past = r then v ξ i past else 0

omit [MeasurableSpace Ξ] in
theorem mixedInnovation_selectedDirection
    (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R) (r : R)
    (i : Fin M) (w : Ξ × (Fin M → Bool)) :
    mixedInnovation (selectedDirection v label r) i w =
      if label w.1 i (signPrefix i w.2) = r then mixedInnovation v i w else 0 := by
  simp only [mixedInnovation,signedInnovation,selectedDirection]
  split_ifs <;> simp

theorem selectedInnovation_integrable
    (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R) (r : R) (i : Fin M)
    (hl : MeasurableSet {w : Ξ × (Fin M → Bool) | label w.1 i (signPrefix i w.2) = r})
    (hi : Integrable (mixedInnovation v i) (η.prod (signLaw M))) :
    Integrable (mixedInnovation (selectedDirection v label r) i) (η.prod (signLaw M)) := by
  convert hi.indicator hl using 1
  funext w
  simp only [mixedInnovation_selectedDirection,Set.indicator,Set.mem_setOf_eq]

theorem selectedInnovation_second_moment
    (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R) (r : R) (i : Fin M)
    (hl : MeasurableSet {w : Ξ × (Fin M → Bool) | label w.1 i (signPrefix i w.2) = r})
    (hi : Integrable (fun w => ‖mixedInnovation v i w‖^2) (η.prod (signLaw M))) :
    Integrable (fun w => ‖mixedInnovation (selectedDirection v label r) i w‖^2) (η.prod (signLaw M)) := by
  convert hi.indicator hl using 1
  funext w
  simp only [mixedInnovation_selectedDirection,Set.indicator,Set.mem_setOf_eq]
  split_ifs <;> simp

/-- Select each physical innovation using a label fixed before its new sign,
then sum the selected physical times. Random epoch/local-time addresses are
one instance; selecting by a future completed-node event is not. -/
def reindexedInnovation (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R) (r : R)
    (w : Ξ × (Fin M → Bool)) : E :=
  ∑ i, mixedInnovation (selectedDirection v label r) i w

theorem reindexedInnovation_integrable
    (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R) (r : R)
    (hl : ∀ i, MeasurableSet {w : Ξ × (Fin M → Bool) | label w.1 i (signPrefix i w.2) = r})
    (hi : ∀ i, Integrable (mixedInnovation v i) (η.prod (signLaw M))) :
    Integrable (reindexedInnovation v label r) (η.prod (signLaw M)) :=
  integrable_finset_sum _ (fun i _ => selectedInnovation_integrable v label r i (hl i) (hi i))

theorem reindexedInnovation_second_moment
    (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R) (r : R)
    (hl : ∀ i, MeasurableSet {w : Ξ × (Fin M → Bool) | label w.1 i (signPrefix i w.2) = r})
    (hi : ∀ i, Integrable (mixedInnovation v i) (η.prod (signLaw M)))
    (hi2 : ∀ i, Integrable (fun w => ‖mixedInnovation v i w‖^2) (η.prod (signLaw M))) :
    Integrable (fun w => ‖reindexedInnovation v label r w‖^2) (η.prod (signLaw M)) :=
  integrable_norm_sum_sq _ _
    (fun i _ => selectedInnovation_integrable v label r i (hl i) (hi i))
    (fun i _ => selectedInnovation_second_moment v label r i (hl i) (hi2 i))

/-- Distinct predictable labels produce orthogonal sums, even when their
physical time indices are random and depend on the earlier signs. -/
theorem reindexedInnovation_orthogonal
    (v : Ξ → (i : Fin M) → (Fin i.val → Bool) → E)
    (label : Ξ → (i : Fin M) → (Fin i.val → Bool) → R)
    (hl : ∀ r i, MeasurableSet {w : Ξ × (Fin M → Bool) | label w.1 i (signPrefix i w.2) = r})
    (hi : ∀ i, Integrable (mixedInnovation v i) (η.prod (signLaw M)))
    (hi2 : ∀ i, Integrable (fun w => ‖mixedInnovation v i w‖^2) (η.prod (signLaw M)))
    (r s : R) (hrs : r ≠ s) :
    (∫ w, ⟪reindexedInnovation v label r w,reindexedInnovation v label s w⟫_ℝ ∂η.prod (signLaw M)) = 0 := by
  have hv (r : R) (i : Fin M) := selectedInnovation_integrable v label r i (hl r i) (hi i)
  have hv2 (r : R) (i : Fin M) := selectedInnovation_second_moment v label r i (hl r i) (hi2 i)
  have hc (i j : Fin M) := integrable_inner_of_second_moments (hv r i) (hv s j) (hv2 r i) (hv2 s j)
  simp only [reindexedInnovation]
  simp_rw [sum_inner]
  simp_rw [inner_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hc i j))]
  apply Finset.sum_eq_zero
  intro i hi'
  rw [integral_finset_sum _ (fun j _ => hc i j)]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : i=j
  · subst j
    have hz (w : Ξ × (Fin M → Bool)) :
        ⟪mixedInnovation (selectedDirection v label r) i w,
          mixedInnovation (selectedDirection v label s) i w⟫_ℝ = 0 := by
      simp only [mixedInnovation_selectedDirection]
      split_ifs with hr hs hs <;> simp_all
    simp_rw [hz]
    simp
  · exact mixedInnovation_cross_orthogonal _ _ i j hij (hv r i) (hv s j) (hv2 r i) (hv2 s j)

end
end SecondOrder
