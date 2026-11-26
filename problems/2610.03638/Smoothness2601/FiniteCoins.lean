import Smoothness2601.PrefixSimulator
import Bilevel.MultiscaleActivation

/-! The simulator's Boolean paths are the actual finite independent draws.
This bridges its state recursion and reveal count to the probability model. -/
noncomputable section
namespace Smoothness2601.PrefixSimulator
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws

def coinSequence : (N : ℕ) → Draws Bool N → ℕ → Bool
  | 0,_ => fun _ => false
  | n+1,z => fun t => if t < n then coinSequence n z.1 t else if t = n then z.2 else false

theorem coinSequence_prefix (n : ℕ) (z : Draws Bool (n+1)) (t : ℕ) (ht : t < n) :
    coinSequence (n+1) z t = coinSequence n z.1 t := by simp [coinSequence,ht]

theorem coinSequence_last (n : ℕ) (z : Draws Bool (n+1)) : coinSequence (n+1) z n = z.2 := by
  simp [coinSequence]

instance drawsBoolCountable (N : ℕ) : Countable (Draws Bool N) := by
  induction N with
  | zero => exact inferInstanceAs (Countable PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Countable (Draws Bool n × Bool))

instance drawsBoolSingleton (N : ℕ) : MeasurableSingletonClass (Draws Bool N) := by
  induction N with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSingletonClass (Draws Bool n × Bool))

theorem prefixCount_congr (T N : ℕ) {c e : ℕ → Bool} (he : ∀ t < N, c t = e t) :
    prefixCount T c N = prefixCount T e N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [prefixCount,he N (Nat.lt_succ_self N),ih (fun t ht => he t (Nat.lt_succ_of_lt ht))]

def successCount : (N : ℕ) → Draws Bool N → ℕ
  | 0,_ => 0
  | n+1,z => successCount n z.1+if z.2 then 1 else 0

theorem successCount_cast (N : ℕ) (z : Draws Bool N) :
    (successCount N z : ℝ) = MultiscaleActivation.count N z := by
  induction N with
  | zero => simp [successCount,MultiscaleActivation.count]
  | succ n ih =>
    simp only [successCount,MultiscaleActivation.count,Nat.cast_add,ih]
    cases z.2 <;> simp

theorem prefixCount_sequence (T N : ℕ) (z : Draws Bool N) :
    prefixCount T (coinSequence N z) N = min T (successCount N z) := by
  induction N with
  | zero => simp [prefixCount,successCount]
  | succ n ih =>
    rw [prefixCount,coinSequence_last]
    rw [prefixCount_congr T n (fun t ht => coinSequence_prefix n z t ht),ih]
    change min T (min T (successCount n z.1)+(if z.2 then 1 else 0)) =
      min T (successCount n z.1+(if z.2 then 1 else 0))
    omega

theorem unsaturated_of_count_lt (T N : ℕ) (z : Draws Bool N)
    (h : MultiscaleActivation.count N z < T) : prefixCount T (coinSequence N z) N < T := by
  rw [prefixCount_sequence]
  have hc : successCount N z < T := by rw [← successCount_cast] at h; exact_mod_cast h
  exact (min_le_right _ _).trans_lt hc

theorem saturation_probability (N T : ℕ) (hT : 0 < T) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (law (Bilevel.BernoulliOracle.law q hq1) N).real
      {z | T ≤ prefixCount T (coinSequence N z) N} ≤ (N : ℝ)*q/T := by
  have he : {z : Draws Bool N | T ≤ prefixCount T (coinSequence N z) N} =
      {z | (T : ℝ) ≤ MultiscaleActivation.count N z} := by
    ext z
    rw [Set.mem_setOf_eq,prefixCount_sequence,le_min_iff]
    simp only [le_refl,true_and,Set.mem_setOf_eq,← successCount_cast]
    exact_mod_cast (Iff.rfl : T ≤ successCount N z ↔ T ≤ successCount N z)
  rw [he]
  exact MultiscaleActivation.full_revelation_probability N q hq0 hq1 T (Nat.cast_pos.mpr hT)

theorem saturation_probability_eighth (N T : ℕ) (hT : 0 < T) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbudget : (N : ℝ)*q ≤ T/8) :
    (law (Bilevel.BernoulliOracle.law q hq1) N).real
      {z | T ≤ prefixCount T (coinSequence N z) N} ≤ 1/8 := by
  apply (saturation_probability N T hT q hq0 hq1).trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr hT)).mpr
  linarith

variable {d T : ℕ} (A : Adaptive.Algorithm (Space d) ℝ)
variable (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)

theorem realState_coins_congr {c e : ℕ → Bool} (N : ℕ) (he : ∀ t < N, c t = e t)
    (initial : A.Memory) (U : Frame d T) :
    realState A reply c initial U N = realState A reply e initial U N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [realState,he N (Nat.lt_succ_self N),ih (fun t ht => he t (Nat.lt_succ_of_lt ht))]

theorem realState_eq_independent_run (N : ℕ) (z : Draws Bool N) (initial : A.Memory) (U : Frame d T) :
    realState A reply (coinSequence N z) initial U N =
      IndependentDraws.run A.query (fun t m v => A.update t (m,v)) (reply U) initial N z := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [realState,IndependentDraws.run,coinSequence_last]
    rw [realState_coins_congr A reply n (fun t ht => coinSequence_prefix n z t ht),ih]

end Smoothness2601.PrefixSimulator
