import SampleReuse.RandomFrameProbability

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory RandomizedFO2003 Rotations
open scoped InnerProductSpace

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def prefixIndex {m N : ℕ} (hN : N < m) (r : Fin (N+1)) : Fin r.val → Fin m :=
  fun i => ⟨i.val, by omega⟩

/-- Exactly the query/output union pattern in the manuscript: stage `r` sees
the first `r` columns, and tests all columns `j ≥ r`. There are `N` call stages
and the additional stage `N` for an arbitrary output. The theorem includes
`N = 0` and does not require query or output norms to be bounded. -/
theorem sequential_frame_tail {m N : ℕ} (hN : N < m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : Fin m → E) (he : Orthonormal ℝ e)
    (q : ∀ r : Fin (N+1), Ω × (Fin r.val → E) → E) (hq : ∀ r, Measurable (q r))
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (μ.prod (haarLaw E)).real {p | ∃ r : Fin (N+1), ∃ j : Fin m, r.val ≤ j.val ∧
      ‖q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k)))‖ ≤ R ∧
      t ≤ |⟪q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k))),
        isometry E p.2 (e j)⟫_ℝ|} ≤
      ((m : ℝ) * (N+1)) *
        (2 * Real.exp (-((Module.finrank ℝ E - N : ℕ) : ℝ) * t ^ 2 / (2 * R ^ 2))) := by
  let α := {p : Fin (N+1) × Fin m // p.1.val ≤ p.2.val}
  have ha (r : α) : Function.Injective (prefixIndex hN r.val.1) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin m => z.val) hij
  have hj (r : α) (k : Fin r.val.1.val) : prefixIndex hN r.val.1 k ≠ r.val.2 := by
    intro heq
    have hv := congrArg Fin.val heq
    have hr := r.property
    simp only [prefixIndex] at hv
    omega
  have hD (r : α) : Module.finrank ℝ E - N ≤
      Module.finrank ℝ E - Fintype.card (Fin r.val.1.val) := by
    simp only [Fintype.card_fin]
    have hr := r.val.1.isLt
    omega
  have htail := adaptive_frame_union_tail μ e he (fun r : α => Fin r.val.1.val)
    (fun r => prefixIndex hN r.val.1) ha (fun r => r.val.2) hj
    (fun r => q r.val.1) (fun r => hq r.val.1) hD hR ht
  have hevent : {p : Ω × Rotation E | ∃ r : Fin (N+1), ∃ j : Fin m, r.val ≤ j.val ∧
      ‖q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k)))‖ ≤ R ∧
      t ≤ |⟪q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k))),
        isometry E p.2 (e j)⟫_ℝ|} =
      {p | ∃ r : α,
        ‖q r.val.1 (p.1, fun k => isometry E p.2 (e (prefixIndex hN r.val.1 k)))‖ ≤ R ∧
        t ≤ |⟪q r.val.1 (p.1, fun k => isometry E p.2 (e (prefixIndex hN r.val.1 k))),
          isometry E p.2 (e r.val.2)⟫_ℝ|} := by
    ext p
    constructor
    · rintro ⟨r, j, hrj, hr, htj⟩
      exact ⟨⟨(r,j), hrj⟩, hr, htj⟩
    · rintro ⟨r, hr, htj⟩
      exact ⟨r.val.1, r.val.2, r.property, hr, htj⟩
  rw [hevent]
  apply htail.trans
  have hcard : Fintype.card α ≤ m * (N+1) := by
    calc
      _ ≤ Fintype.card (Fin (N+1) × Fin m) := Fintype.card_subtype_le _
      _ = _ := by simp [Nat.mul_comm]
  have hcardR : (Fintype.card α : ℝ) ≤ (m : ℝ) * (N+1) := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hcardR (by positivity)

end SampleReuse.RandomFrame
