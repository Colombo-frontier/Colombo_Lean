import Bilevel.GenieTheorem

/-! A finite public dimension exists for any positive projection target
and fixed observation horizon. This deliberately makes no sharp claim
about the manuscript's displayed ambient-dimension expression. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.SourceObserverBudget

theorem exists_increment (M R T : ℕ) (hM : 0<M) (hT : 0<T)
    (δ cap : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hc : 0<cap) :
    ∃ r : ℕ, ∃ b : ℝ, 0<r ∧ 0<b ∧ b≤2 ∧ (R:ℝ)*((M:ℝ)*b)≤1/2 ∧
      2*(M:ℝ)*b≤cap ∧ (M:ℝ≥0∞)*GenieProtocol.failurePerQuery T r b=ENNReal.ofReal (δ/2) := by
  have hMr : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  let a : ℝ := min 1 (min (1/(2*((R:ℝ)+1)*M)) (cap/(2*M)))
  have ha : 0<a := by dsimp [a];positivity
  let r : ℕ := ⌈(8*Real.log (4*(M:ℝ)*T/δ))/a⌉₊+1
  have hr : 0<r := Nat.zero_lt_succ _
  have hrr : 0<(r:ℝ) := Nat.cast_pos.mpr hr
  let b := GenieProtocol.logarithmicIncrement M T r δ
  have hb : 0<b := GenieProtocol.logarithmic_increment_pos M T r hM hT hr δ hδ hδ1
  have hceil : (8*Real.log (4*(M:ℝ)*T/δ))/a≤(r:ℝ) := by
    have h := Nat.le_ceil ((8*Real.log (4*(M:ℝ)*T/δ))/a)
    dsimp [r]
    rw [Nat.cast_add,Nat.cast_one]
    linarith
  have hba : b≤a := by
    dsimp [b,GenieProtocol.logarithmicIncrement]
    apply (div_le_iff₀ hrr).mpr
    have h := (div_le_iff₀ ha).mp hceil
    nlinarith
  have ha1 : a≤1 := min_le_left _ _
  have har : a≤1/(2*((R:ℝ)+1)*M) := (min_le_right _ _).trans (min_le_left _ _)
  have hac : a≤cap/(2*M) := (min_le_right _ _).trans (min_le_right _ _)
  have hden : 0<2*((R:ℝ)+1)*M := by positivity
  have hprod := (le_div_iff₀ hden).mp har
  have hprod' := (le_div_iff₀ (by positivity : 0<2*(M:ℝ))).mp hac
  have hRb : (R:ℝ)*((M:ℝ)*b)≤(R:ℝ)*((M:ℝ)*a) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hba hMr.le) (Nat.cast_nonneg R)
  have hMa : 0<(M:ℝ)*a := mul_pos hMr ha
  have hCb := mul_le_mul_of_nonneg_left hba (by positivity : 0≤2*(M:ℝ))
  refine ⟨r,b,hr,hb,by linarith,by nlinarith,by nlinarith,?_⟩
  rw [GenieProtocol.failurePerQuery,←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg M)]
  exact congrArg ENNReal.ofReal (GenieProtocol.logarithmic_failure_identity M T r hM hT hr δ hδ)

theorem exists_dimension (D₀ M R T : ℕ) (hM : 0<M) (hT : 0<T)
    (δ cap : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hc : 0<cap) :
    ∃ D r : ℕ, ∃ b : ℝ, D₀≤D ∧ T≤D ∧ M+R+(r+1)≤D ∧
      0<r ∧ 0<b ∧ b≤2 ∧ (R:ℝ)*((M:ℝ)*b)≤1/2 ∧ 2*(M:ℝ)*b≤cap ∧
      (M:ℝ≥0∞)*GenieProtocol.failurePerQuery T r b=ENNReal.ofReal (δ/2) := by
  obtain ⟨r,b,hr,hb,hb2,hcap,henergy,hprob⟩ := exists_increment M R T hM hT δ cap hδ hδ1 hc
  exact ⟨D₀+T+M+R+(r+1),r,b,by omega,by omega,by omega,hr,hb,hb2,hcap,henergy,hprob⟩

end Bilevel.SourceObserverBudget
