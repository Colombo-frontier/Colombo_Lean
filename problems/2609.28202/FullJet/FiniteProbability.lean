import FullJet.ProductInformation

open scoped BigOperators ENNReal

namespace FullJet

theorem pmf_toReal_sum {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

theorem pmf_event_toReal {α : Type*} [Fintype α] (p : PMF α) (A : Set α)
    [DecidablePred (· ∈ A)] :
    (p.toOuterMeasure A).toReal = ∑ a, if a ∈ A then (p a).toReal else 0 := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a ha
    by_cases h : a ∈ A <;> simp [h]
  · intro a ha
    by_cases h : a ∈ A <;> simp [h, p.apply_ne_top a]

theorem pmf_event_compl_toReal {α : Type*} [Fintype α] (p : PMF α) (A : Set α) :
    (p.toOuterMeasure Aᶜ).toReal = 1 - (p.toOuterMeasure A).toReal := by
  classical
  have h : (p.toOuterMeasure Aᶜ).toReal + (p.toOuterMeasure A).toReal = 1 := by
    rw [pmf_event_toReal, pmf_event_toReal, ← Finset.sum_add_distrib]
    trans ∑ a, (p a).toReal
    · apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a ∈ A <;> simp [h]
    · exact pmf_toReal_sum p
  linarith

theorem pmf_decide_event {α : Type*} [Fintype α] (p : PMF α) (A : Set α)
    [DecidablePred (· ∈ A)] (b : Bool) :
    ((p.map (fun x => decide (x ∈ A))) b).toReal = bitWeight ((p.toOuterMeasure A).toReal) b := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  cases b
  · have hset : (fun x => decide (x ∈ A)) ⁻¹' ({false} : Set Bool) = Aᶜ := by ext x; simp
    rw [hset, pmf_event_compl_toReal]
    rfl
  · have hset : (fun x => decide (x ∈ A)) ⁻¹' ({true} : Set Bool) = A := by ext x; simp
    rw [hset]
    rfl

theorem uniformPi_map_coordinates {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : ι → Finset α) (hs : ∀ j, (s j).Nonempty) (f : ι → α → β) (b : ι → β) :
    (((uniformPi s hs).map (fun x j => f j (x j))) b).toReal =
      ∏ j, (((PMF.uniformOfFinset (s j) (hs j)).map (f j)) (b j)).toReal := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hset : (fun (x : ι → α) j => f j (x j)) ⁻¹' ({b} : Set (ι → β)) = {x | ∀ j, f j (x j) = b j} := by
    ext x
    simp [funext_iff]
  have hrect := uniformPi_rect_probability s hs (fun j => {x | f j x = b j})
  simp only [Set.mem_setOf_eq] at hrect
  rw [hset, hrect]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

theorem pmf_event_pos_of_support {α : Type*} (p : PMF α) (A : Set α)
    (hA : ∃ x ∈ A, x ∈ p.support) : 0 < (p.toOuterMeasure A).toReal := by
  apply ENNReal.toReal_pos
  · intro hz
    have hd := (p.toOuterMeasure_apply_eq_zero_iff A).mp hz
    obtain ⟨x, hxA, hxp⟩ := hA
    exact Set.disjoint_left.mp hd hxp hxA
  · rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top A

theorem pmf_event_zero_of_no_support {α : Type*} (p : PMF α) (A : Set α)
    (hA : ¬ ∃ x ∈ A, x ∈ p.support) : (p.toOuterMeasure A).toReal = 0 := by
  have hz : p.toOuterMeasure A = 0 := (p.toOuterMeasure_apply_eq_zero_iff A).mpr
    (Set.disjoint_left.mpr (fun x hxp hxA => hA ⟨x, hxA, hxp⟩))
  rw [hz, ENNReal.toReal_zero]

theorem pmf_filter_event_toReal {α : Type*} [Fintype α] (p : PMF α) (A B : Set α)
    (hA : ∃ x ∈ A, x ∈ p.support) :
    ((p.filter A hA).toOuterMeasure B).toReal =
      (p.toOuterMeasure (A ∩ B)).toReal / (p.toOuterMeasure A).toReal := by
  classical
  have hpoint (x : α) : ((p.filter A hA) x).toReal =
      if x ∈ A then (p x).toReal / (p.toOuterMeasure A).toReal else 0 := by
    rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
    by_cases hx : x ∈ A <;> simp [hx, div_eq_mul_inv]
  rw [pmf_event_toReal, pmf_event_toReal, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hpoint]
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]

theorem pmf_event_chain {α : Type*} [Fintype α] (p : PMF α) (A B : Set α)
    (hA : ∃ x ∈ A, x ∈ p.support) :
    (p.toOuterMeasure (A ∩ B)).toReal =
      (p.toOuterMeasure A).toReal * ((p.filter A hA).toOuterMeasure B).toReal := by
  rw [pmf_filter_event_toReal]
  exact (mul_div_cancel₀ _ (pmf_event_pos_of_support p A hA).ne').symm

theorem pmf_map_congr_on_support {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  classical
  ext b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · simp [(p.apply_eq_zero_iff x).mpr hx]

theorem pmf_map_eq_pure_of_support {α β : Type*} (p : PMF α) (f : α → β) (b : β)
    (h : ∀ x ∈ p.support, f x = b) : p.map f = PMF.pure b :=
  (pmf_map_congr_on_support p f (Function.const α b) h).trans (PMF.map_const p b)

end FullJet
