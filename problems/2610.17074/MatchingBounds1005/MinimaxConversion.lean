import MatchingBounds1005.OracleMeasurability
import Mathlib.Algebra.Order.Floor.Semiring

/-! Exact conversion from distributional hardness and deterministic algorithms
to the manuscript's extended-real, dimension-uniform minimax statement.
This module does not assert either main bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MatchingBounds1005.Model

theorem transcript_prefix {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (f : Space d → ℝ) (seed : Seed)
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    transcript A f seed n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ =
      transcript A f seed m i := by
  induction n with
  | zero => have : m = 0 := Nat.eq_zero_of_le_zero hmn; subst m; exact Fin.elim0 i
  | succ n ih =>
    by_cases heq : m = n + 1
    · subst m; rfl
    · have hmn' : m ≤ n := by omega
      have hi : (⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ : Fin (n + 1)) =
          Fin.castSucc (⟨i.val, lt_of_lt_of_le i.isLt hmn'⟩ : Fin n) := rfl
      rw [transcript, hi, Fin.snoc_castSucc]
      exact ih hmn'

def padAlgorithm {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (T : ℕ) : Algorithm d Seed where
  query := A.query
  output n seed hist := if h : T ≤ n then
    A.output T seed (fun i => hist ⟨i.val, lt_of_lt_of_le i.isLt h⟩)
    else A.output n seed hist
  query_measurable := A.query_measurable
  output_measurable n := by
    by_cases h : T ≤ n
    · simp only [h, dite_true]
      have hg : Measurable (fun z : Seed × (Fin n → Response d) =>
          fun i : Fin T => z.2 ⟨i.val, lt_of_lt_of_le i.isLt h⟩) := by
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply (⟨i.val, lt_of_lt_of_le i.isLt h⟩ : Fin n)).comp measurable_snd
      exact (A.output_measurable T).comp (measurable_fst.prodMk hg)
    · simpa only [h, dite_false] using A.output_measurable n

theorem padAlgorithm_transcript {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (T : ℕ) (f : Space d → ℝ) (seed : Seed) (n : ℕ) :
    transcript (padAlgorithm A T) f seed n = transcript A f seed n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [transcript, ih]; rfl

theorem padAlgorithm_success {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) {T N : ℕ} (hTN : T ≤ N) (f : Space d → ℝ) (ε : ℝ) :
    Success (padAlgorithm A T) f ε N = Success A f ε T := by
  ext seed
  simp only [Success, Set.mem_setOf_eq, padAlgorithm_transcript]
  change (‖gradient f (if h : T ≤ N then A.output T seed
    (fun i => transcript A f seed N ⟨i.val, lt_of_lt_of_le i.isLt h⟩)
    else A.output N seed (transcript A f seed N))‖ ≤ ε) ↔ _
  simp only [hTN, dite_true, transcript_prefix]

theorem randomizedCap_mono {p d T N : ℕ} {ε : ℝ} (hTN : T ≤ N)
    (h : RandomizedCap p d ε T) : RandomizedCap p d ε N := by
  rcases h with ⟨Seed, ms, sb, ν, hp, A, hA⟩
  letI := ms
  letI := sb
  letI := hp
  refine ⟨Seed, ms, sb, ν, hp, padAlgorithm A T, ?_⟩
  intro f hf
  rw [padAlgorithm_success A hTN]
  exact hA f hf

theorem deterministicCap_randomized {p d T : ℕ} {ε : ℝ}
    (h : DeterministicCap p d ε T) : RandomizedCap p d ε T := by
  rcases h with ⟨A, hA⟩
  refine ⟨Unit, inferInstance, inferInstance, Measure.dirac (), inferInstance, A, ?_⟩
  intro f hf
  have hs : Success A f ε T = Set.univ := by
    ext seed
    cases seed
    simp [hA f hf]
  rw [hs, measure_univ]
  exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)

theorem hardDistribution_not_randomizedCap {p d T : ℕ} {ε : ℝ}
    (h : HardDistribution p d T ε) : ¬ RandomizedCap p d ε T := by
  rcases h with ⟨Ω, msΩ, sbΩ, μ, hpμ, F, hF, hclass, hhard⟩
  letI := msΩ
  letI := sbΩ
  letI := hpμ
  rintro ⟨Seed, ms, sb, ν, hpν, A, hA⟩
  letI := ms
  letI := sb
  letI := hpν
  obtain ⟨hmeas, hsmall⟩ := hhard Seed ν A
  have hlarge : (2 / 3 : ℝ≥0∞) ≤
      (μ.prod ν) {z : Ω × Seed | z.2 ∈ Success A (F z.1) ε T} := by
    rw [Measure.prod_apply hmeas]
    calc
      (2 / 3 : ℝ≥0∞) = ∫⁻ _ : Ω, (2 / 3 : ℝ≥0∞) ∂μ := by simp
      _ ≤ _ := lintegral_mono fun sample => hA (F sample) (hclass sample)
  have := ENNReal.toReal_mono (by norm_num : (1 / 3 : ℝ≥0∞) ≠ ⊤)
    (hlarge.trans hsmall)
  norm_num at this

theorem hardDistribution_lt_cap {p d T N : ℕ} {ε : ℝ}
    (h : HardDistribution p d T ε) (hN : RandomizedCap p d ε N) : T < N := by
  by_contra hn
  exact hardDistribution_not_randomizedCap h (randomizedCap_mono (by omega) hN)

theorem randomizedQueries_le_deterministic (p d : ℕ) (ε : ℝ) :
    randomizedQueries p d ε ≤ deterministicQueries p d ε := by
  apply sInf_le_sInf
  rintro x ⟨T, rfl, hT⟩
  exact ⟨T, rfl, deterministicCap_randomized hT⟩

theorem randomizedQueriesUniform_le_deterministic (p : ℕ) (ε : ℝ) :
    randomizedQueriesUniform p ε ≤ deterministicQueriesUniform p ε :=
  iSup_mono fun d => randomizedQueries_le_deterministic p (d + 1) ε

theorem deterministicQueries_le_cap {p d T : ℕ} {ε : ℝ}
    (h : DeterministicCap p d ε T) : deterministicQueries p d ε ≤ (T : ℝ≥0∞) :=
  sInf_le ⟨T, rfl, h⟩

theorem hardDistribution_queries_lower {p d : ℕ} {ε x : ℝ}
    (h : HardDistribution p d ⌊x⌋₊ ε) :
    ENNReal.ofReal x ≤ randomizedQueries p d ε := by
  apply le_sInf
  rintro _ ⟨T, rfl, hT⟩
  have hreal : x ≤ (T : ℝ) := (Nat.lt_of_floor_lt (hardDistribution_lt_cap h hT)).le
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal

theorem mainMinimax_of_bounds (hl : MainLowerBound) (hu : MainUpperBound) :
    MainMinimaxTheorem := by
  intro p hp
  obtain ⟨c, Cd, el, hc, hCd, hel, hl⟩ := hl p hp
  obtain ⟨C, eu, hC, heu, hu⟩ := hu p hp
  refine ⟨c, C, min el eu, hc, hC, lt_min hel heu, ?_⟩
  intro ε hε hsmall
  obtain ⟨d, hd, _, hhard⟩ := hl ε hε (hsmall.trans (min_le_left _ _))
  refine ⟨?_, randomizedQueriesUniform_le_deterministic p ε, ?_⟩
  · calc
      ENNReal.ofReal (c * rate ε) ≤ randomizedQueries p d ε :=
        hardDistribution_queries_lower hhard
      _ ≤ randomizedQueriesUniform p ε := by
        have heq : d - 1 + 1 = d := by omega
        simpa only [heq] using
          (le_iSup (fun n => randomizedQueries p (n + 1) ε) (d - 1))
  · apply iSup_le
    intro n
    obtain ⟨T, A, hT, hA⟩ := hu ε hε (hsmall.trans (min_le_right _ _)) (n + 1) (by omega)
    calc
      deterministicQueries p (n + 1) ε ≤ (T : ℝ≥0∞) :=
        deterministicQueries_le_cap ⟨A, hA⟩
      _ ≤ ENNReal.ofReal (C * rate ε * Real.log (2 / ε)) := by
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hT

theorem mainTheorem_of_bounds (hl : MainLowerBound) (hu : MainUpperBound) :
    MainTheorem := ⟨hl, hu, mainMinimax_of_bounds hl hu⟩

end MatchingBounds1005.Model
