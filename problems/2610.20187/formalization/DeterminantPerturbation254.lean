import GaussianState254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem finite_product_abs_bound {ι : Type*} (s : Finset ι) (f : ι→ℝ) (B : ℝ)
    (hB : 0≤B) (hf : ∀ i∈s,|f i|≤B) : |∏ i∈s,f i|≤B^s.card := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i∈s,B := Finset.prod_le_prod (fun _ _=>abs_nonneg _) hf
    _ = _ := by simp

/-- A deliberately conservative bound whose logarithm is polynomial in
the number of factors and their encoding lengths. -/
theorem finite_product_difference_bound {ι : Type*} (s : Finset ι)
    (f g : ι→ℝ) (B e : ℝ) (hB : 1≤B) (he : 0≤e)
    (hf : ∀ i∈s,|f i|≤B) (hg : ∀ i∈s,|g i|≤B)
    (hfg : ∀ i∈s,|f i-g i|≤e) :
    |(∏ i∈s,f i)-(∏ i∈s,g i)|≤s.card*e*B^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs := ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))
      (fun j hj=>hg j (Finset.mem_insert_of_mem hj))
      (fun j hj=>hfg j (Finset.mem_insert_of_mem hj))
    have hp := finite_product_abs_bound s g B (by linarith)
      (fun j hj=>hg j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hdiff := hfg i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,pow_succ]
    have hid : f i*(∏ j∈s,f j)-g i*(∏ j∈s,g j)=
        f i*((∏ j∈s,f j)-(∏ j∈s,g j))+(f i-g i)*(∏ j∈s,g j) := by ring
    rw [hid]
    calc
      _ ≤ |f i| * |(∏ j∈s,f j)-(∏ j∈s,g j)|+|f i-g i| * |∏ j∈s,g j| := by
        simpa only [abs_mul] using abs_add_le
          (f i*((∏ j∈s,f j)-(∏ j∈s,g j))) ((f i-g i)*(∏ j∈s,g j))
      _ ≤ B*(s.card*e*B^s.card)+e*B^s.card := by gcongr
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hB (show 0≤e*B^s.card by positivity)
        nlinarith

theorem determinant_entry_perturbation {d : ℕ} (A B : Precision d) (M e : ℝ)
    (hM : 1≤M) (he : 0≤e) (hA : ∀ i j,|A i j|≤M) (hB : ∀ i j,|B i j|≤M)
    (hAB : ∀ i j,|A i j-B i j|≤e) :
    |A.det-B.det|≤(Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*e*M^d := by
  rw [Matrix.det_apply,Matrix.det_apply,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d),|Equiv.Perm.sign σ • (∏ i,A (σ i) i)-
        Equiv.Perm.sign σ • (∏ i,B (σ i) i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d),(d:ℝ)*e*M^d := by
      apply Finset.sum_le_sum
      intro σ _
      have hh := finite_product_difference_bound Finset.univ
        (fun i=>A (σ i) i) (fun i=>B (σ i) i) M e hM he
        (fun i _=>hA _ _) (fun i _=>hB _ _) (fun i _=>hAB _ _)
      rw [← smul_sub]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simpa [hs] using hh
      · simpa only [hs,Units.smul_def,Units.val_neg,Units.val_one,neg_smul,one_smul,
          abs_neg,Finset.card_univ,Fintype.card_fin] using hh
    _ = _ := by simp; ring

theorem real_log_difference_bound (x y l : ℝ) (hl : 0<l) (hx : l≤x) (hy : l≤y) :
    |Real.log x-Real.log y|≤|x-y|/l := by
  have hx0 := hl.trans_le hx
  have hy0 := hl.trans_le hy
  have oneSide : ∀ a b : ℝ,l≤b → b≤a → Real.log a-Real.log b≤(a-b)/l := by
    intro a b hb hab
    have hb0 := hl.trans_le hb
    have ha0 := hb0.trans_le hab
    have hh := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    rw [Real.log_div ha0.ne' hb0.ne'] at hh
    have he : a/b-1=(a-b)/b := by field_simp
    rw [he] at hh
    exact hh.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hl hb)
  by_cases hxy : y≤x
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy)),abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact oneSide x y hy hxy
  · have hyx := le_of_not_ge hxy
    rw [abs_sub_comm (Real.log x),abs_sub_comm x,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx0 hyx)),abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact oneSide y x hx hyx

theorem logdet_entry_perturbation {d : ℕ} (A B : Precision d) (M e l : ℝ)
    (hM : 1≤M) (he : 0≤e) (hl : 0<l) (hdetA : l≤A.det) (hdetB : l≤B.det)
    (hA : ∀ i j,|A i j|≤M) (hB : ∀ i j,|B i j|≤M)
    (hAB : ∀ i j,|A i j-B i j|≤e) :
    |Real.log A.det-Real.log B.det|≤(Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*e*M^d/l :=
  (real_log_difference_bound _ _ _ hl hdetA hdetB).trans
    (div_le_div_of_nonneg_right (determinant_entry_perturbation A B M e hM he hA hB hAB) hl.le)

end Paper254
#print axioms Paper254.logdet_entry_perturbation
