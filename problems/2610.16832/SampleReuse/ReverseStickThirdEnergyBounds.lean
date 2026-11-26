import SampleReuse.ReverseStickThirdScoreBounds

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section

theorem sqrt_four_product_le {a b A B : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (haA : a ≤ A ^ 2) (hbB : b ≤ B ^ 2) :
    Real.sqrt (4 * (a * b)) ≤ 2 * A * B := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  calc
    4 * (a * b) ≤ 4 * (A ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul haA hbB hb (sq_nonneg _)) (by norm_num)
    _ = (2 * A * B) ^ 2 := by ring

theorem sqrt_twentyseven_product_le {a b c A B C : ℝ}
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (haA : a ≤ A ^ 2) (hbB : b ≤ B ^ 2) (hcC : c ≤ C ^ 2) :
    Real.sqrt (27 * (a * b * c)) ≤ 6 * A * B * C := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  calc
    27 * (a * b * c) ≤ 27 * (A ^ 2 * B ^ 2 * C ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul haA hbB hb (sq_nonneg _)) hcC hc
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num)
    _ ≤ (6 * A * B * C) ^ 2 := by nlinarith [sq_nonneg (A * B * C)]

variable {ι : Type*} [Fintype ι]

theorem bernoulliThirdScore_abs_mean_le_of_energies
    (p a b c ab ac bc abc : ι → ℝ) (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (A B C AB AC BC ABC : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAB : 0 ≤ AB) (hAC : 0 ≤ AC) (hBC : 0 ≤ BC)
    (ha : bernoulliFisherEnergy p a ≤ A ^ 2)
    (hb : bernoulliFisherEnergy p b ≤ B ^ 2)
    (hc : bernoulliFisherEnergy p c ≤ C ^ 2)
    (hab : bernoulliFisherEnergy p ab ≤ AB ^ 2)
    (hac : bernoulliFisherEnergy p ac ≤ AC ^ 2)
    (hbc : bernoulliFisherEnergy p bc ≤ BC ^ 2)
    (habc : (∑ i, |abc i|) ≤ ABC) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
      (fun w => |bernoulliThirdScore p a b c ab ac bc abc w|) ≤
      2 * ABC + 2 * AB * C + 2 * AC * B + 2 * BC * A + 6 * A * B * C := by
  have hnonneg (q : ι → ℝ) := bernoulliFisherEnergy_nonneg p q hp0 hp1
  exact (bernoulliThirdScore_abs_mean_le p a b c ab ac bc abc hp0 hp1).trans
    (add_le_add (add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left habc (by norm_num))
        (sqrt_four_product_le (hnonneg ab) (hnonneg c) hAB hC hab hc))
      (sqrt_four_product_le (hnonneg ac) (hnonneg b) hAC hB hac hb))
      (sqrt_four_product_le (hnonneg bc) (hnonneg a) hBC hA hbc ha))
      (sqrt_twentyseven_product_le (hnonneg a) (hnonneg b) (hnonneg c) hA hB hC ha hb hc))

end
end SampleReuse
