import SecondOrder.FiniteLawTransport

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

theorem pmfMean_map (p : PMF α) (f : α → β) (X : β → ℝ) :
    pmfMean (p.map f) X = pmfMean p (fun a => X (f a)) := by
  simp only [pmfMean, smul_eq_mul, PMF.map_apply, tsum_fintype]
  have hs (b : β) : (∑ a, if b = f a then p a else 0).toReal =
      ∑ a, (if b = f a then p a else 0).toReal :=
    ENNReal.toReal_sum (fun a _ => by by_cases h : b = f a <;> simp [h, p.apply_ne_top])
  simp_rw [hs, apply_ite ENNReal.toReal, ENNReal.toReal_zero, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem pmf_map_ne_zero (p : PMF α) (hp : ∀ a, p a ≠ 0)
    {f : α → β} (hf : Function.Surjective f) (b : β) : p.map f b ≠ 0 := by
  obtain ⟨a, rfl⟩ := hf b
  apply ((p.map f).mem_support_iff (f a)).mp
  exact (PMF.mem_support_map_iff f p (f a)).mpr
    ⟨a, (p.mem_support_iff a).mpr (hp a), rfl⟩

/-- A deterministic response cannot increase finite relative entropy.
Surjectivity only chooses the response support; both input laws have full support. -/
theorem pmfKL_map_le (p q : PMF α) (hp : ∀ a, p a ≠ 0) (hq : ∀ a, q a ≠ 0)
    {f : α → β} (hf : Function.Surjective f) : pmfKL (p.map f) (q.map f) ≤ pmfKL p q := by
  have hpr (a : α) : 0 < (p a).toReal := ENNReal.toReal_pos (hp a) (p.apply_ne_top a)
  have hqr (a : α) : 0 < (q a).toReal := ENNReal.toReal_pos (hq a) (q.apply_ne_top a)
  have hPr (b : β) : 0 < (p.map f b).toReal :=
    ENNReal.toReal_pos (pmf_map_ne_zero p hp hf b) ((p.map f).apply_ne_top b)
  have hQr (b : β) : 0 < (q.map f b).toReal :=
    ENNReal.toReal_pos (pmf_map_ne_zero q hq hf b) ((q.map f).apply_ne_top b)
  have hpoint (a : α) :
      (p a).toReal*Real.log ((p.map f (f a)).toReal/(q.map f (f a)).toReal) ≤
        (p a).toReal*Real.log ((p a).toReal/(q a).toReal) +
        (q a).toReal*((p.map f (f a)).toReal/(q.map f (f a)).toReal) - (p a).toReal := by
    have hratio : 0 < ((p.map f (f a)).toReal/(q.map f (f a)).toReal)/
        ((p a).toReal/(q a).toReal) := div_pos (div_pos (hPr _) (hQr _)) (div_pos (hpr _) (hqr _))
    have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) (hpr a).le
    rw [Real.log_div (div_pos (hPr _) (hQr _)).ne' (div_pos (hpr _) (hqr _)).ne'] at hlog
    have he : (p a).toReal*(((p.map f (f a)).toReal/(q.map f (f a)).toReal)/
        ((p a).toReal/(q a).toReal)-1) =
        (q a).toReal*((p.map f (f a)).toReal/(q.map f (f a)).toReal)-(p a).toReal := by
      have halg (s t u v : ℝ) (hs : s ≠ 0) (ht : t ≠ 0) (hv : v ≠ 0) :
          s*((u/v)/(s/t)-1) = t*(u/v)-s := by field_simp; ring
      exact halg _ _ _ _ (hpr a).ne' (hqr a).ne' (hQr (f a)).ne' 
    rw [he] at hlog
    linarith
  have hcancel : pmfMean (q.map f) (fun b => (p.map f b).toReal/(q.map f b).toReal) = 1 := by
    unfold pmfMean
    simp only [smul_eq_mul, mul_div_cancel₀ _ (hQr _).ne']
    exact pmf_toReal_sum (p.map f)
  change pmfMean (p.map f) (fun b => Real.log ((p.map f b).toReal/(q.map f b).toReal)) ≤ _
  rw [pmfMean_map]
  change (∑ a, (p a).toReal*Real.log ((p.map f (f a)).toReal/(q.map f (f a)).toReal)) ≤ _
  apply (Finset.sum_le_sum (fun a _ => hpoint a)).trans
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, pmf_toReal_sum]
  change pmfKL p q + pmfMean q (fun a => (p.map f (f a)).toReal/(q.map f (f a)).toReal)-1 ≤ _
  rw [← pmfMean_map q f (fun b => (p.map f b).toReal/(q.map f b).toReal), hcancel]
  simp

theorem klDiv_pmf_map_le [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p q : PMF α) (hp : ∀ a, p a ≠ 0) (hq : ∀ a, q a ≠ 0)
    {f : α → β} (hf : Function.Surjective f) :
    klDiv (p.map f).toMeasure (q.map f).toMeasure ≤ klDiv p.toMeasure q.toMeasure := by
  rw [klDiv_pmf _ _ (pmf_map_ne_zero q hq hf), klDiv_pmf p q hq]
  exact ENNReal.ofReal_le_ofReal (pmfKL_map_le p q hp hq hf)

end
end SecondOrder
