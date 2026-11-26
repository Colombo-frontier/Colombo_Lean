import NCConcave16991.ConditionalHaarConeMachineProbability
import NCConcave16991.ConditionalHaarConeMachineProbe
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Concrete finite cone probe event and an actual small Haar probability

All three bounded probes are tested at every outer boundary t≤T and every
component row. The Haar dimension is explicit and unrestricted by the problem
model; a polynomial dimension makes the genuine Chebyshev union bound ≤1/6.
-/

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def probeCount (n T : ℕ) : ℕ := 3 * ((T + 1) * n)
abbrev ProbeIndex (n T : ℕ) := Fin 3 × Fin (T + 1) × Fin n

def probeEncoding (n T : ℕ) : ProbeIndex n T ≃ Fin (probeCount n T) :=
  (Equiv.prodCongr (Equiv.refl (Fin 3))
    (finProdFinEquiv : Fin (T + 1) × Fin n ≃ Fin ((T + 1) * n))).trans finProdFinEquiv

def probeKind (n T : ℕ) (a : Fin (probeCount n T)) : Fin 3 := ((probeEncoding n T).symm a).1
def probeOuterTime (n T : ℕ) (a : Fin (probeCount n T)) : Fin (T + 1) := ((probeEncoding n T).symm a).2.1
def probeRow (n T : ℕ) (a : Fin (probeCount n T)) : Fin n := ((probeEncoding n T).symm a).2.2
def probeTime (n T : ℕ) (a : Fin (probeCount n T)) : ℕ := (n + 2) * (probeOuterTime n T a).val

@[simp] theorem probeKind_encoded (n T : ℕ) (b : Fin 3) (t : Fin (T + 1)) (i : Fin n) :
    probeKind n T (probeEncoding n T (b,t,i)) = b := by simp [probeKind]

@[simp] theorem probeTime_encoded (n T : ℕ) (b : Fin 3) (t : Fin (T + 1)) (i : Fin n) :
    probeTime n T (probeEncoding n T (b,t,i)) = (n + 2) * t.val := by simp [probeTime, probeOuterTime]

@[simp] theorem probeRow_encoded (n T : ℕ) (b : Fin 3) (t : Fin (T + 1)) (i : Fin n) :
    probeRow n T (probeEncoding n T (b,t,i)) = i := by simp [probeRow]

theorem probeTime_le (n T : ℕ) (a : Fin (probeCount n T)) : probeTime n T a ≤ (n + 2) * T :=
  Nat.mul_le_mul_left (n + 2) (Nat.le_of_lt_succ (probeOuterTime n T a).isLt)

def leakRadius (n : ℕ) : ℝ := 1 / (64 * Real.sqrt (n : ℝ))

theorem leakRadius_pos {n : ℕ} (hn : 0 < n) : 0 < leakRadius n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold leakRadius
  positivity

theorem leakRadius_sq {n : ℕ} (hn : 0 < n) : leakRadius n ^ 2 = 1 / (4096 * (n : ℝ)) := by
  unfold leakRadius
  rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  norm_num

def hardDimension (n M T : ℕ) : ℕ :=
  (n + 2) * T + n + 1 + 221184 * n * (M + 1) * probeCount n T

theorem hardDimension_gt_budget (n M T : ℕ) : (n + 2) * T < hardDimension n M T := by
  unfold hardDimension
  omega

theorem hardDimension_ge_rows (n M T : ℕ) : n ≤ hardDimension n M T := by
  unfold hardDimension
  omega

theorem hardDimension_gap (n M T : ℕ) :
    221184 * n * (M + 1) * probeCount n T ≤ hardDimension n M T - (n + 2) * T := by
  unfold hardDimension
  omega

def hardEmbedding (n M T : ℕ) : Fin n ↪ Fin (hardDimension n M T) where
  toFun i := ⟨i.val, i.isLt.trans_le (hardDimension_ge_rows n M T)⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun a : Fin (hardDimension n M T) ↦ a.val) h

variable (k n M : ℕ) (R : ℝ) (hR : 0 < R)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain (FrameSpace k) M R hR) (n := n)
    (dx := ConeProblem.primalDimension (FrameSpace k) M) Ω)

def finiteProbe (hn : 0 < n) (T : ℕ) (j : Fin (M + 1)) (a : Fin (probeCount n T))
    (seed : Ω) (s : State (FrameSpace k) n M R hR) : FrameSpace k :=
  if (probeKind n T a).val = 0 then querySourceProbe (FrameSpace k) n M R hR P seed hn j s else
  if (probeKind n T a).val = 1 then queryClockProbe (FrameSpace k) n M R hR P seed hn j s else
    finalSourceProbe (FrameSpace k) n M R hR P seed j s

theorem finiteProbe_measurable (hn : 0 < n) (T : ℕ) (j : Fin (M + 1)) (a : Fin (probeCount n T)) :
    Measurable (Function.uncurry (finiteProbe k n M R hR P hn T j a)) := by
  unfold finiteProbe
  split_ifs
  · exact querySourceProbe_measurable (FrameSpace k) n M R hR P hn j
  · exact queryClockProbe_measurable (FrameSpace k) n M R hR P hn j
  · exact finalSourceProbe_measurable (FrameSpace k) n M R hR P j

theorem finiteProbe_norm_le (hn : 0 < n) (T : ℕ) (j : Fin (M + 1)) (a : Fin (probeCount n T))
    (seed : Ω) (s : State (FrameSpace k) n M R hR) : ‖finiteProbe k n M R hR P hn T j a seed s‖ ≤ 3 := by
  unfold finiteProbe
  split_ifs
  · exact querySourceProbe_norm_le (FrameSpace k) n M R hR P seed hn j s
  · exact (queryClockProbe_norm_le (FrameSpace k) n M R hR P seed hn j s).trans (by norm_num)
  · exact (finalSourceProbe_norm_le (FrameSpace k) n M R hR P seed j s).trans (by norm_num)

def badEvent (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k) (T : ℕ) :
    Set (Ω × (Fin (M + 1) → OrthogonalGroup k)) :=
  allStageBad k n M R hR P hn q e (probeTime n T) (finiteProbe k n M R hR P hn T)
    (probeRow n T) (leakRadius n)

theorem badEvent_measurable (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k) (T : ℕ) :
    MeasurableSet (badEvent k n M R hR P hn q e T) :=
  allStageBad_measurable k n M R hR P hn q e (probeTime n T) (finiteProbe k n M R hR P hn T)
    (finiteProbe_measurable k n M R hR P hn T) (probeRow n T) (leakRadius n)

theorem badEvent_mass_le (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k) (T : ℕ) (hbudget : (n + 2) * T < k) :
    (ν.prod (rotationLaw k (M + 1))).real (badEvent k n M R hR P hn q e T) ≤
      (M + 1 : ℝ) * (probeCount n T : ℝ) * 9 /
        (((k - (n + 2) * T : ℕ) : ℝ) * leakRadius n ^ 2) := by
  have h := allStageBad_mass_le k n M R hR P ν hn q e ((n + 2) * T) hbudget
    (probeTime n T) (probeTime_le n T) (finiteProbe k n M R hR P hn T)
    (finiteProbe_measurable k n M R hR P hn T) (C := 3) (by norm_num)
    (finiteProbe_norm_le k n M R hR P hn T) (probeRow n T) (leakRadius_pos hn)
  simpa only [badEvent, show (3 : ℝ) ^ 2 = 9 by norm_num] using h

theorem badEvent_mass_le_one_sixth (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k) (T : ℕ) (hbudget : (n + 2) * T < k)
    (hdim : 221184 * n * (M + 1) * probeCount n T ≤ k - (n + 2) * T) :
    (ν.prod (rotationLaw k (M + 1))).real (badEvent k n M R hR P hn q e T) ≤ 1 / 6 := by
  apply (badEvent_mass_le k n M R hR P ν hn q e T hbudget).trans
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (k - (n + 2) * T : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hbudget
  have hg : (221184 : ℝ) * (n : ℝ) * (M + 1 : ℝ) * (probeCount n T : ℝ) ≤
      ((k - (n + 2) * T : ℕ) : ℝ) := by exact_mod_cast hdim
  rw [leakRadius_sq hn]
  have he : (M + 1 : ℝ) * (probeCount n T : ℝ) * 9 /
      (((k - (n + 2) * T : ℕ) : ℝ) * (1 / (4096 * (n : ℝ)))) =
      ((M + 1 : ℝ) * (probeCount n T : ℝ) * 9 * 4096 * (n : ℝ)) /
        ((k - (n + 2) * T : ℕ) : ℝ) := by field_simp [hd.ne', hn0.ne']
  rw [he]
  apply (div_le_iff₀ hd).mpr
  nlinarith

end

end NCConcave16991.Haar.ConeMachine
