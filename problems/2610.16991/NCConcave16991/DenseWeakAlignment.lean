import NCConcave16991.DenseWeakRademacher

/-! # Actual product-law probability of finitely many adaptive alignment vectors -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

namespace FiniteLaw

variable {I A H : Type*} [Fintype I] [Fintype A] [Fintype H]

theorem eventMass_mono (P : FiniteLaw I) {E F : Set I} (h : E ⊆ F) :
    P.eventMass E ≤ P.eventMass F := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ E
  · simp only [eventMass, if_pos hi, if_pos (h hi)]
    exact le_rfl
  · simp only [if_neg hi]
    by_cases hf : i ∈ F
    · simp only [if_pos hf]
      exact P.nonneg i
    · simp only [if_neg hf]
      exact le_rfl

theorem eventMass_exists_le (P : FiniteLaw I) (E : A → Set I) :
    P.eventMass {i | ∃ a, i ∈ E a} ≤ ∑ a, P.eventMass (E a) := by
  classical
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : ∃ a, i ∈ E a
  · obtain ⟨a, ha⟩ := hi
    rw [if_pos (show i ∈ {i | ∃ a, i ∈ E a} from ⟨a,ha⟩)]
    have hs := Finset.single_le_sum (s := (Finset.univ : Finset A))
      (f := fun b ↦ if i ∈ E b then P.mass i else 0)
      (fun b _ ↦ by split_ifs; exact P.nonneg i; exact le_rfl) (Finset.mem_univ a)
    simpa only [if_pos ha] using hs
  · rw [if_neg (show i ∉ {i | ∃ a, i ∈ E a} from hi)]
    exact Finset.sum_nonneg (fun a _ ↦ by split_ifs; exact P.nonneg i; exact le_rfl)

theorem product_eventMass (P : FiniteLaw I) (Q : FiniteLaw H) (E : Set (I × H)) :
    (P.product Q).eventMass E = ∑ h, Q.mass h * P.eventMass {i | (i,h) ∈ E} := by
  classical
  unfold eventMass
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i,h) ∈ E <;> simp [hi, product, mul_comm]

end FiniteLaw

def alignmentEvent {D B : ℕ} {H : Type*} (v : H → Fin B → Fin D → ℝ) (a : ℝ) :
    Set ((Fin D → Fin 2) × H) := {z | ∃ t, a ≤ signedSum (v z.2 t) z.1}

theorem product_alignment_bound {D B : ℕ} {H : Type*} [Fintype H]
    (Q : FiniteLaw H) (v : H → Fin B → Fin D → ℝ)
    (hv : ∀ h t, (∑ j, (v h t j) ^ 2) ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    ((rademacherLaw D).product Q).eventMass (alignmentEvent v a) ≤
      (B : ℝ) * Real.exp (-a ^ 2 / 2) := by
  rw [FiniteLaw.product_eventMass]
  have hpoint (h : H) : (rademacherLaw D).eventMass
      {θ | (θ,h) ∈ alignmentEvent v a} ≤ (B : ℝ) * Real.exp (-a ^ 2 / 2) := by
    calc
      _ ≤ ∑ t : Fin B, (rademacherLaw D).eventMass {θ | a ≤ signedSum (v h t) θ} :=
        FiniteLaw.eventMass_exists_le _ (fun t ↦ {θ | a ≤ signedSum (v h t) θ})
      _ ≤ ∑ _t : Fin B, Real.exp (-a ^ 2 / 2) :=
        Finset.sum_le_sum (fun t _ ↦ rademacher_tail (v h t) (hv h t) a ha)
      _ = _ := by simp
  calc
    _ ≤ ∑ h, Q.mass h * ((B : ℝ) * Real.exp (-a ^ 2 / 2)) :=
      Finset.sum_le_sum (fun h _ ↦ mul_le_mul_of_nonneg_left (hpoint h) (Q.nonneg h))
    _ = _ := by rw [← Finset.sum_mul, Q.sum_one, one_mul]

theorem product_gate_alignment_bound {D B : ℕ} {H : Type*} [Fintype H]
    (Q : FiniteLaw H) (v : H → Fin B → Fin D → ℝ)
    (hv : ∀ h t, (∑ j, (v h t j) ^ 2) ≤ 1) :
    ((rademacherLaw D).product Q).eventMass
      (alignmentEvent v ((5 / 32 : ℝ) * Real.sqrt (D : ℝ))) ≤
      (B : ℝ) * Real.exp (-25 * (D : ℝ) / 2048) := by
  have hh := product_alignment_bound Q v hv ((5 / 32 : ℝ) * Real.sqrt (D : ℝ)) (by positivity)
  have he : -((5 / 32 : ℝ) * Real.sqrt (D : ℝ)) ^ 2 / 2 = -25 * (D : ℝ) / 2048 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg D)]
    ring
  rwa [he] at hh

end NCConcave16991.DenseWeakHiding
