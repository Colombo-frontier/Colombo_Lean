import Nonsmooth.DyadicPeakLegality

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def orderBetter (o : ResponseOrder 4) (i j : Fin 4) : Fin 4 := if o j i then i else j

def orderBestFour (o : ResponseOrder 4) : Fin 4 :=
  orderBetter o (orderBetter o (orderBetter o 0 1) 2) 3

def bestFourResponse (v : Fin 4 → ℝ) : Fin 4 :=
  orderBestFour (responseOrder (fun i : Fin 4 => ((), v i)))

theorem orderBetter_value_bounds (v : Fin 4 → ℝ) (i j : Fin 4) :
    let k := orderBetter (responseOrder (fun i : Fin 4 => ((), v i))) i j
    v i ≤ v k ∧ v j ≤ v k := by
  by_cases h : v j ≤ v i
  · simpa [orderBetter, responseOrder, h] using And.intro (le_rfl : v i ≤ v i) h
  · simpa [orderBetter, responseOrder, h] using
      And.intro (le_of_lt (lt_of_not_ge h)) (le_rfl : v j ≤ v j)

theorem bestFourResponse_max (v : Fin 4 → ℝ) (i : Fin 4) : v i ≤ v (bestFourResponse v) := by
  let o := responseOrder (fun i : Fin 4 => ((), v i))
  let i1 := orderBetter o 0 1
  let i2 := orderBetter o i1 2
  have h1 := orderBetter_value_bounds v 0 1
  have h2 := orderBetter_value_bounds v i1 2
  have h3 := orderBetter_value_bounds v i2 3
  fin_cases i
  · exact h1.1.trans (h2.1.trans h3.1)
  · exact h1.2.trans (h2.1.trans h3.1)
  · exact h2.2.trans h3.1
  · exact h3.2

theorem bestFourResponse_measurable : Measurable bestFourResponse := by
  have hm : Measurable (fun v : Fin 4 → ℝ => fun i : Fin 4 => ((), v i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_const.prodMk (measurable_pi_apply i)
  exact (measurable_of_countable orderBestFour).comp ((responseOrder_measurable 4).comp hm)

theorem bestFourResponse_add_const (v : Fin 4 → ℝ) (c : ℝ) :
    bestFourResponse (fun i => v i + c) = bestFourResponse v := by
  unfold bestFourResponse
  congr 1
  funext i j
  simp only [responseOrder, add_le_add_iff_right]

theorem periodic_four_peak_bracket (f : ℤ → ℝ) (L : ℤ)
    (hp : Function.Periodic f (4 * L)) (i : Fin 4)
    (hm : ∀ j : Fin 4, f ((j.val : ℤ) * L) ≤ f ((i.val : ℤ) * L)) :
    f ((i.val : ℤ) * L - L) ≤ f ((i.val : ℤ) * L) ∧
      f ((i.val : ℤ) * L + L) ≤ f ((i.val : ℤ) * L) := by
  have hminus : f (-L) = f (3 * L) := by
    have h := hp (-L)
    have he : -L + 4 * L = 3 * L := by ring
    rw [he] at h
    exact h.symm
  have hplus : f (4 * L) = f 0 := by simpa using hp 0
  have h0 : f 0 ≤ f ((i.val : ℤ) * L) := by simpa using hm 0
  have h1 : f L ≤ f ((i.val : ℤ) * L) := by simpa using hm 1
  have h2 : f (2 * L) ≤ f ((i.val : ℤ) * L) := hm 2
  have h3 : f (3 * L) ≤ f ((i.val : ℤ) * L) := hm 3
  fin_cases i <;> norm_num at h0 h1 h2 h3 ⊢
  · constructor
    · simpa only [hminus] using h3
    · exact h1
  · constructor
    · exact h0
    · convert h2 using 1 <;> congr 1 <;> ring
  · constructor
    · convert h1 using 1 <;> congr 1 <;> ring
    · convert h3 using 1 <;> congr 1 <;> ring
  · constructor
    · convert h2 using 1 <;> congr 1 <;> ring
    · have he : (3 : ℤ) * L + L = 4 * L := by ring
      rw [he, hplus]
      exact h0

def cyclicDyadicPeak (f : ℤ → ℝ) (N : ℕ) : ℤ :=
  dyadicPeakSearch f N ((bestFourResponse (fun i => f ((i.val : ℤ) * 2 ^ N))).val * 2 ^ N)

theorem cyclicDyadicPeak_local_max (f : ℤ → ℝ) (N : ℕ)
    (hp : Function.Periodic f (4 * 2 ^ N)) :
    f (cyclicDyadicPeak f N - 1) ≤ f (cyclicDyadicPeak f N) ∧
      f (cyclicDyadicPeak f N + 1) ≤ f (cyclicDyadicPeak f N) := by
  have hb := periodic_four_peak_bracket f (2 ^ N) hp
    (bestFourResponse (fun i => f ((i.val : ℤ) * 2 ^ N)))
    (fun j => bestFourResponse_max (fun i => f ((i.val : ℤ) * 2 ^ N)) j)
  exact dyadicPeakSearch_local_max f N _ hb.1 hb.2

end
end Nonsmooth
