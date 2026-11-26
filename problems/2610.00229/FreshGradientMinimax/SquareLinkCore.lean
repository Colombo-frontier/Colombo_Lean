import FreshGradientMinimax.CoreGate

/-! The actual scalar chain (22), its square-link identity (23), and the
dimension-linear value bound. The length is n+1 and links are indexed by Fin n. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def coreLinkPlus (a b : ℝ) : ℝ := Real.sqrt (coreGate (-a) * coreTheta (-b))
def coreLinkMinus (a b : ℝ) : ℝ := Real.sqrt (coreGate a * (coreThetaMass - coreTheta b))
def coreLinkTerm (a b : ℝ) : ℝ := coreGate (-a) * coreTheta (-b) - coreGate a * coreTheta b

theorem coreLinkPlus_sq (a b : ℝ) : coreLinkPlus a b ^ 2 = coreGate (-a) * coreTheta (-b) :=
  Real.sq_sqrt (mul_nonneg (coreGate_nonneg _) (coreTheta_pos _).le)

theorem coreLinkMinus_sq (a b : ℝ) :
    coreLinkMinus a b ^ 2 = coreGate a * (coreThetaMass - coreTheta b) :=
  Real.sq_sqrt (mul_nonneg (coreGate_nonneg _) (sub_nonneg.mpr (coreTheta_le_mass _)))

theorem coreLink_square_identity (a b : ℝ) :
    coreLinkPlus a b ^ 2 + coreLinkMinus a b ^ 2 = coreLinkTerm a b + coreThetaMass * coreGate a := by
  rw [coreLinkPlus_sq, coreLinkMinus_sq]
  unfold coreLinkTerm
  ring

theorem coreLinkPlus_bound (a b : ℝ) : |coreLinkPlus a b| ≤ 4 := by
  have hs := coreLinkPlus_sq a b
  have hn : 0 ≤ coreLinkPlus a b := Real.sqrt_nonneg _
  have hp : coreGate (-a) * coreTheta (-b) ≤ 9 := by
    have h := mul_le_mul (coreGate_le_three (-a)) (coreTheta_lt_three (-b)).le
      (coreTheta_pos (-b)).le (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h
    exact h
  rw [abs_of_nonneg hn]
  nlinarith

theorem coreLinkMinus_bound (a b : ℝ) : |coreLinkMinus a b| ≤ 4 := by
  have hs := coreLinkMinus_sq a b
  have hn : 0 ≤ coreLinkMinus a b := Real.sqrt_nonneg _
  have ht0 : 0 ≤ coreThetaMass - coreTheta b := sub_nonneg.mpr (coreTheta_le_mass _)
  have ht3 : coreThetaMass - coreTheta b ≤ 3 := by
    linarith [coreThetaMass_lt_three, coreTheta_pos b]
  have hp : coreGate a * (coreThetaMass - coreTheta b) ≤ 9 := by
    have h := mul_le_mul (coreGate_le_three a) ht3 ht0 (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h
    exact h
  rw [abs_of_nonneg hn]
  nlinarith

theorem coreLinkTerm_bound (a b : ℝ) : |coreLinkTerm a b| ≤ 9 := by
  have hpos (s t : ℝ) : 0 ≤ coreGate s * coreTheta t :=
    mul_nonneg (coreGate_nonneg _) (coreTheta_pos _).le
  have hle (s t : ℝ) : coreGate s * coreTheta t ≤ 9 := by
    have h := mul_le_mul (coreGate_le_three s) (coreTheta_lt_three t).le
      (coreTheta_pos t).le (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h
    exact h
  apply abs_le.mpr
  unfold coreLinkTerm
  constructor <;> linarith [hpos a b, hpos (-a) (-b), hle a b, hle (-a) (-b)]

theorem coreLinks_flat {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) :
    coreLinkPlus a b = 0 ∧ coreLinkMinus a b = 0 ∧ coreLinkTerm a b = 0 := by
  obtain ⟨hp, hm⟩ := coreGate_flat ha
  simp [coreLinkPlus, coreLinkMinus, coreLinkTerm, hp, hm]

def squareLinkCore {n : ℕ} (u : Fin (n + 1) → ℝ) : ℝ :=
  -coreTheta (u 0) + ∑ i : Fin n, coreLinkTerm (u i.castSucc) (u i.succ)

def squareLinkSeed {n : ℕ} (u : Fin (n + 1) → ℝ) : ℝ :=
  -coreTheta (u 0) - coreThetaMass * ∑ i : Fin n, coreGate (u i.castSucc)

theorem squareLinkCore_identity {n : ℕ} (u : Fin (n + 1) → ℝ) :
    squareLinkCore u = squareLinkSeed u + ∑ i : Fin n,
      (coreLinkPlus (u i.castSucc) (u i.succ) ^ 2 + coreLinkMinus (u i.castSucc) (u i.succ) ^ 2) := by
  simp_rw [coreLink_square_identity]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold squareLinkCore squareLinkSeed
  ring

theorem squareLinkCore_bound {n : ℕ} (u : Fin (n + 1) → ℝ) :
    |squareLinkCore u| ≤ 9 * (n + 1 : ℝ) := by
  have hseed : |coreTheta (u 0)| ≤ 3 := by
    rw [abs_of_pos (coreTheta_pos _)]
    exact (coreTheta_lt_three _).le
  have hsum : (∑ i : Fin n, |coreLinkTerm (u i.castSucc) (u i.succ)|) ≤ 9 * (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (9 : ℝ) := Finset.sum_le_sum (fun i _ => coreLinkTerm_bound _ _)
      _ = _ := by simp; ring
  unfold squareLinkCore
  have h := abs_add_le (-coreTheta (u 0)) (∑ i : Fin n, coreLinkTerm (u i.castSucc) (u i.succ))
  rw [abs_neg] at h
  have ha := Finset.abs_sum_le_sum_abs (fun i : Fin n => coreLinkTerm (u i.castSucc) (u i.succ)) Finset.univ
  linarith

theorem squareLinkCore_zero (n : ℕ) : squareLinkCore (fun _ : Fin (n + 1) => 0) = -coreTheta 0 := by
  have hf := (coreLinks_flat (by norm_num : |(0 : ℝ)| ≤ 1 / 2) 0).2.2
  simp [squareLinkCore, hf]

theorem squareLinkSeed_le_core {n : ℕ} (u : Fin (n + 1) → ℝ) : squareLinkSeed u ≤ squareLinkCore u := by
  rw [squareLinkCore_identity]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))

end FreshGradientMinimax
