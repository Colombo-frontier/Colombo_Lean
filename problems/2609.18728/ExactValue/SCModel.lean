import ExactValue.MainTheorems

open scoped ENNReal InnerProductSpace
set_option autoImplicit false

namespace ExactValue
noncomputable section

/-- The public strongly convex class of the September 2026 manuscript. -/
structure SCObjective (d : ℕ) (μ β R : ℝ) (f : Euclid d → ℝ) : Prop extends
    AdmissibleObjective d β R f where
  strong : StrongConvexOn Set.univ μ f

theorem AdmissibleObjective.smooth_mono {d : ℕ} {β₀ β R : ℝ} {f : Euclid d → ℝ}
    (hf : AdmissibleObjective d β₀ R f) (hβ : β₀ ≤ β) : AdmissibleObjective d β R f := by
  refine ⟨hf.convex, hf.contDiff, ?_, hf.minimizer⟩
  obtain ⟨G, hG, hLip⟩ := hf.gradient_lipschitz
  exact ⟨G, hG, fun x y => (hLip x y).trans (mul_le_mul_of_nonneg_right hβ (norm_nonneg _))⟩

theorem strong_supporting {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d} {μ : ℝ}
    (hs : StrongConvexOn Set.univ μ f)
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) (x y : Euclid d) :
    f y + ⟪G y, x - y⟫_ℝ + μ / 2 * ‖x - y‖ ^ 2 ≤ f x := by
  have hd (z : Euclid d) : HasFDerivAt (fun z => f z - μ / 2 * ‖z‖ ^ 2)
      (innerSL ℝ (G z - μ • z)) z := by
    convert (hder z).sub (((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_mul (μ / 2)) using 1
    ext w
    simp [innerSL_apply, inner_sub_left, real_inner_smul_left]
    ring
  have h := convex_supporting (strongConvexOn_iff_convex.mp hs) hd x y
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [inner_sub_right, norm_sub_sq_real, real_inner_comm y x]
  nlinarith

theorem convex_of_supporting {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d}
    (hs : ∀ x y, f y + ⟪G y, x - y⟫_ℝ ≤ f x) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hs x z) ha
  have hy := mul_le_mul_of_nonneg_left (hs y z) hb
  have hz : a • (x - z) + b • (y - z) = 0 := by
    rw [smul_sub, smul_sub]
    calc
      _ = a • x + b • y - (a + b) • z := by rw [add_smul]; abel
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hi := congrArg (fun w => ⟪G z, w⟫_ℝ) hz
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  change f z ≤ a * f x + b * f y
  have hsum : a * f z + b * f z = f z := by rw [← add_mul, hab, one_mul]
  nlinarith

theorem strong_iff_supporting {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d} {μ : ℝ}
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) :
    StrongConvexOn Set.univ μ f ↔
      ∀ x y, f y + ⟪G y, x - y⟫_ℝ + μ / 2 * ‖x - y‖ ^ 2 ≤ f x := by
  constructor
  · exact fun hs x y => strong_supporting hs hder x y
  · intro hs
    rw [strongConvexOn_iff_convex]
    apply convex_of_supporting (G := fun y => G y - μ • y)
    intro x y
    have h := hs x y
    rw [inner_sub_right, norm_sub_sq_real, real_inner_comm y x] at h
    simp only [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
    nlinarith

def ValueAlgorithm.SCGuarantees {d T : ℕ} {μ β R ε : ℝ} (A : ValueAlgorithm d R T) : Prop :=
  ∀ f, SCObjective d μ β R f → ∃ xstar : Euclid d,
    (∀ y, f xstar ≤ f y) ∧ f (A.result f) - f xstar ≤ ε

def scValueComplexity (d : ℕ) (R μ β ε : ℝ) : ℝ≥0∞ :=
  ⨅ T : ℕ, ⨅ A : ValueAlgorithm d R T, ⨅ (_ : A.SCGuarantees (μ := μ) (β := β) (ε := ε)),
    (T : ℝ≥0∞)

theorem scValueComplexity_le {d T : ℕ} {μ β R ε : ℝ} (A : ValueAlgorithm d R T)
    (hA : A.SCGuarantees (μ := μ) (β := β) (ε := ε)) : scValueComplexity d R μ β ε ≤ T :=
  iInf_le_of_le T (iInf_le_of_le A (iInf_le_of_le hA le_rfl))

theorem scValueComplexity_le_convex {d : ℕ} {R μ β ε : ℝ} :
    scValueComplexity d R μ β ε ≤ valueComplexity d R β ε := by
  apply le_iInf
  intro T
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  exact scValueComplexity_le A (fun f hf => hA f hf.toAdmissibleObjective)

theorem sc_direct_upper {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    scValueComplexity d R μ β ε ≤ ENNReal.ofReal (6 * d * Real.sqrt (β * R ^ 2 / ε)) :=
  scValueComplexity_le_convex.trans (valueComplexity_upper hd hβ hR hε hεmax)

theorem sc_lower_of_failure {d : ℕ} {R μ β ε c : ℝ}
    (hfail : ∀ T : ℕ, (T : ℝ) < c → ∀ A : ValueAlgorithm d R T,
      ¬ A.SCGuarantees (μ := μ) (β := β) (ε := ε)) :
    ENNReal.ofReal c ≤ scValueComplexity d R μ β ε := by
  apply le_iInf
  intro T
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  have hreal : c ≤ (T : ℝ) := by
    by_contra hc
    exact hfail T (lt_of_not_ge hc) A hA
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal

end
end ExactValue
