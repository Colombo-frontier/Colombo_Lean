import RandomizedFO2003.MainThetaBound
import RandomizedFO2003.AlgorithmPadding
import Mathlib.Data.ENat.Lattice
import Mathlib.MeasureTheory.Measure.Dirac

namespace RandomizedFO2003.Model

open MeasureTheory
open scoped ENNReal

/-- Some measurable randomized first-order algorithm succeeds uniformly
on the original function class at the stated exact query budget. -/
def Solvable (d : ℕ) (ε Δ L₁ L₂ : ℝ) (T : ℕ) : Prop :=
  ∃ (Seed : Type) (m : MeasurableSpace Seed) (ν : @Measure Seed m),
    @IsProbabilityMeasure Seed m ν ∧ ∃ A : @Algorithm d Seed m,
      ∀ f : Space d → ℝ, InFunctionClass f Δ L₁ L₂ →
        (2 / 3 : ℝ≥0∞) ≤ ν (@Success d Seed m A f ε T)

/-- The fixed-dimensional minimax query count, infinity if unsolvable. -/
noncomputable def queryComplexity (d : ℕ) (ε Δ L₁ L₂ : ℝ) : ℕ∞ :=
  sInf {q : ℕ∞ | ∃ T : ℕ, (T : ℕ∞) = q ∧ Solvable d ε Δ L₁ L₂ T}

/-- The paper's supremum over all finite dimensions. -/
noncomputable def dimensionFreeComplexity (ε Δ L₁ L₂ : ℝ) : ℕ∞ :=
  ⨆ d : ℕ, queryComplexity d ε Δ L₁ L₂

theorem Solvable.mono {d S T : ℕ} {ε Δ L₁ L₂ : ℝ}
    (h : Solvable d ε Δ L₁ L₂ S) (hST : S ≤ T) : Solvable d ε Δ L₁ L₂ T := by
  obtain ⟨Seed, m, ν, hp, A, hA⟩ := h
  letI := m
  letI := hp
  refine ⟨Seed, m, ν, hp, A.pad S, ?_⟩
  intro f hf
  rw [A.pad_success S T hST f ε]
  exact hA f hf

theorem solvable_of_deterministic {d T : ℕ} {ε Δ L₁ L₂ : ℝ} (A : Algorithm d Unit)
    (hA : ∀ f : Space d → ℝ, InFunctionClass f Δ L₁ L₂ →
      ‖gradient f (A.output T () (transcript A f () T))‖ ≤ ε) : Solvable d ε Δ L₁ L₂ T := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, A, ?_⟩
  intro f hf
  have he : Success A f ε T = Set.univ := by
    ext u
    cases u
    simp only [Success, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hA f hf
  rw [he, measure_univ]
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
  norm_num

theorem queryComplexity_le {d T : ℕ} {ε Δ L₁ L₂ : ℝ}
    (h : Solvable d ε Δ L₁ L₂ T) : queryComplexity d ε Δ L₁ L₂ ≤ (T : ℕ∞) :=
  sInf_le ⟨T, rfl, h⟩

theorem queryComplexity_ge_of_not_solvable {d T : ℕ} {ε Δ L₁ L₂ : ℝ}
    (h : ¬Solvable d ε Δ L₁ L₂ T) : (T + 1 : ℕ) ≤ queryComplexity d ε Δ L₁ L₂ := by
  apply le_sInf
  rintro q ⟨S, rfl, hS⟩
  have hST : T < S := by
    by_contra! hh
    exact h (hS.mono hh)
  exact_mod_cast hST

/-- A precise numerical Θ statement for the actual minimax complexity.
Finiteness is explicit, so converting the extended natural to a natural
number cannot silently turn infinity into zero. -/
def MinimaxThetaBound : Prop :=
  ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 < K ∧
    ∀ ε Δ L₁ L₂ : ℝ, 0 < ε → 0 < Δ → 0 < L₁ → 0 < L₂ →
      ε ≤ c * L₁ ^ 2 / L₂ →
      C ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)) →
      dimensionFreeComplexity ε Δ L₁ L₂ ≠ ⊤ ∧
        c * rate ε Δ L₁ L₂ ≤ ((dimensionFreeComplexity ε Δ L₁ L₂).toNat : ℝ) ∧
        ((dimensionFreeComplexity ε Δ L₁ L₂).toNat : ℝ) ≤ K * rate ε Δ L₁ L₂

theorem minimax_theta_of_operational (hmain : MainThetaBound) : MinimaxThetaBound := by
  obtain ⟨c, C, K, hc, hC, hK, hm⟩ := hmain
  refine ⟨c, C, K, hc, hC, hK, ?_⟩
  intro ε Δ L₁ L₂ hε hΔ hL₁ hL₂ haccuracy hmass
  obtain ⟨hlower, hupper⟩ := hm ε Δ L₁ L₂ hε hΔ hL₁ hL₂ haccuracy hmass
  have hr : 0 < rate ε Δ L₁ L₂ := by unfold rate; positivity
  have hqupper : dimensionFreeComplexity ε Δ L₁ L₂ ≤ (⌊K * rate ε Δ L₁ L₂⌋₊ : ℕ∞) := by
    apply iSup_le
    intro d
    obtain ⟨T, A, hT, hA⟩ := hupper d
    apply (queryComplexity_le (solvable_of_deterministic A hA)).trans
    exact_mod_cast Nat.le_floor hT
  have hfinite : dimensionFreeComplexity ε Δ L₁ L₂ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hqupper
  have hceil : 0 < ⌈c * rate ε Δ L₁ L₂⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos hc hr)
  have htime : ((⌈c * rate ε Δ L₁ L₂⌉₊ - 1 : ℕ) : ℝ) < c * rate ε Δ L₁ L₂ :=
    Nat.lt_ceil.mp (by omega)
  obtain ⟨d, hd⟩ := hlower (⌈c * rate ε Δ L₁ L₂⌉₊ - 1) htime
  have hnot : ¬Solvable d ε Δ L₁ L₂ (⌈c * rate ε Δ L₁ L₂⌉₊ - 1) := by
    rintro ⟨Seed, m, ν, hp, A, hA⟩
    letI := m
    letI := hp
    obtain ⟨f, hf, hbad⟩ := hd Seed ν A
    exact (not_lt_of_ge (hA f hf)) hbad
  have hqlower : (⌈c * rate ε Δ L₁ L₂⌉₊ : ℕ∞) ≤ dimensionFreeComplexity ε Δ L₁ L₂ := by
    have hh := queryComplexity_ge_of_not_solvable hnot
    have he : ⌈c * rate ε Δ L₁ L₂⌉₊ - 1 + 1 = ⌈c * rate ε Δ L₁ L₂⌉₊ := by omega
    rw [he] at hh
    exact hh.trans (le_iSup (queryComplexity · ε Δ L₁ L₂) d)
  refine ⟨hfinite, ?_, ?_⟩
  · have hn := ENat.toNat_le_toNat hqlower hfinite
    simp only [ENat.toNat_coe] at hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  · have hn := ENat.toNat_le_of_le_coe hqupper
    exact (show ((dimensionFreeComplexity ε Δ L₁ L₂).toNat : ℝ) ≤
      (⌊K * rate ε Δ L₁ L₂⌋₊ : ℝ) by exact_mod_cast hn).trans (Nat.floor_le (by positivity))

/-- The paper's full minimax Θ conclusion, derived from both verified
oracle bounds and the proved padding construction. -/
theorem main_minimax_theta_bound : MinimaxThetaBound := minimax_theta_of_operational main_theta_bound

end RandomizedFO2003.Model
