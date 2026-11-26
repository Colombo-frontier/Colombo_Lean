import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Finite stopped energy induction and a public finite dimension choice.
The recurrence is required only while all preceding energy bounds hold.
No future good event is assumed to establish an earlier hypothesis. -/
noncomputable section
namespace Bilevel.TransportObserver

def injection (target C : ℝ) (M : ℕ) : ℝ := target/((M+1)*C^(M+1))

theorem injection_nonneg {target C : ℝ} (ht : 0 ≤ target) (hC : 1 ≤ C) (M : ℕ) :
    0 ≤ injection target C M := by unfold injection; positivity

theorem injection_pos {target C : ℝ} (ht : 0 < target) (hC : 1 ≤ C) (M : ℕ) :
    0 < injection target C M := by unfold injection; positivity

theorem energy_envelope_le_target {target C : ℝ} (ht : 0 ≤ target) (hC : 1 ≤ C)
    (M n : ℕ) (hn : n ≤ M) : (n:ℝ)*C^n*injection target C M ≤ target := by
  have hp : C^n ≤ C^(M+1) := pow_le_pow_right₀ hC (by omega)
  have hn' : (n:ℝ) ≤ (M:ℝ)+1 := by exact_mod_cast (show n ≤ M+1 by omega)
  have hh := mul_le_mul hn' hp (pow_nonneg (by linarith : 0 ≤ C) n) (by positivity : 0 ≤ (M:ℝ)+1)
  have hm := mul_le_mul_of_nonneg_right hh (injection_nonneg ht hC M)
  have hd : (M:ℝ)+1 ≠ 0 := by positivity
  have hCp : C^(M+1) ≠ 0 := pow_ne_zero _ (by linarith : C ≠ 0)
  have he : ((M:ℝ)+1)*C^(M+1)*injection target C M = target := by
    unfold injection
    field_simp
  rwa [he] at hm

/-- Every local bookkeeping energy stays below target, provided its next
update obeys the derived recurrence on the stopped valid prefix. -/
theorem stopped_energy_bound (energy : ℕ → ℝ) {target C : ℝ}
    (ht : 0 ≤ target) (hC : 1 ≤ C) (M : ℕ) (hzero : energy 0 ≤ 0)
    (hstep : ∀ n < M, (∀ j ≤ n, energy j ≤ target) →
      energy (n+1) ≤ C*energy n+injection target C M) :
    ∀ n ≤ M, energy n ≤ target := by
  have hrec : ∀ n ≤ M, energy n ≤ (n:ℝ)*C^n*injection target C M := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero => simpa only [Nat.cast_zero,zero_mul] using hzero
      | succ n =>
        have hp : ∀ j ≤ n, energy j ≤ target := by
          intro j hj
          exact (ih j (by omega) (by omega)).trans (energy_envelope_le_target ht hC M j (by omega))
        have hs := hstep n (by omega) hp
        have hi := mul_le_mul_of_nonneg_left (ih n (by omega) (by omega)) (by linarith : 0 ≤ C)
        have hpow : 1 ≤ C^(n+1) := one_le_pow₀ hC
        have hin := mul_le_mul_of_nonneg_right hpow (injection_nonneg ht hC M)
        push_cast
        rw [pow_succ] at hin ⊢
        nlinarith
  intro n hn
  exact (hrec n hn).trans (energy_envelope_le_target ht hC M n hn)

def ambientDimension (M T d : ℕ) (a : ℝ) : ℕ :=
  Nat.ceil (2*((T:ℝ)+d)+16*M*((T:ℝ)/a+64*(d:ℝ)^2)+1)

/-- A finite dimension chosen only from the horizon, frame size, dimension
cap and public injection target makes the stated local probability sum small.
The actual conditional probability estimates remain separate prerequisites. -/
theorem ambientDimension_budget (M T d : ℕ) {a : ℝ} (ha : 0 < a) :
    let D := (ambientDimension M T d a : ℝ)
    2*((T:ℝ)+d) < D ∧
      M*((T:ℝ)/((D-d)*a)+64*(d:ℝ)^2/(D-T-d)) ≤ 1/8 := by
  let D := (ambientDimension M T d a : ℝ)
  let B := (T:ℝ)/a+64*(d:ℝ)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg T
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hD : 2*((T:ℝ)+d)+16*M*B+1 ≤ D := Nat.le_ceil _
  have hMb : 0 ≤ 16*(M:ℝ)*B := by positivity
  have hstrict : 2*((T:ℝ)+d) < D := by linarith
  have hDp : 0 < D := by linarith
  have hd1 : 0 < D-(d:ℝ) := by linarith
  have hd2 : 0 < D-(T:ℝ)-d := by linarith
  have hb1 : (T:ℝ)/((D-d)*a) ≤ 2*((T:ℝ)/a)/D := by
    rw [show (T:ℝ)/((D-d)*a) = ((T:ℝ)/a)/(D-d) by rw [div_div]; congr 1; ring]
    apply (div_le_div_iff₀ hd1 hDp).mpr
    have hh := mul_nonneg (show 0 ≤ (T:ℝ)/a by positivity)
      (show 0 ≤ D-2*d by linarith)
    nlinarith
  have hb2 : 64*(d:ℝ)^2/(D-T-d) ≤ 2*(64*(d:ℝ)^2)/D := by
    apply (div_le_div_iff₀ hd2 hDp).mpr
    have hh := mul_nonneg (show 0 ≤ 64*(d:ℝ)^2 by positivity)
      (show 0 ≤ D-2*((T:ℝ)+d) by linarith)
    nlinarith
  refine ⟨hstrict,?_⟩
  have hh := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (Nat.cast_nonneg M)
  have hsum : (M:ℝ)*(2*((T:ℝ)/a)/D+2*(64*(d:ℝ)^2)/D) = 2*M*B/D := by dsimp [B]; ring
  rw [hsum] at hh
  apply hh.trans
  apply (div_le_iff₀ hDp).mpr
  have hbD : 16*(M:ℝ)*B ≤ D := by linarith only [hD,hT,hd]
  calc
    2*(M:ℝ)*B = (1/8:ℝ)*(16*M*B) := by ring
    _ ≤ (1/8:ℝ)*D := mul_le_mul_of_nonneg_left hbD (by norm_num)

end Bilevel.TransportObserver
