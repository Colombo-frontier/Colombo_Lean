import Bilevel.TransportRoundExecutedEnergy
import Bilevel.TransportObserverRecurrence

/-! Public finite-horizon energy calibration for the genuine run. An
arbitrarily small requested projection tolerance is allowed. The only event
premise is the explicitly defined actual query/fresh-monitor failure event;
neither a recurrence nor intermediate energy bounds are assumed. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportObserver ProjectionGeometry
set_option maxHeartbeats 800000

def energyTarget (n : ℕ) (b : ℝ) : ℝ := min (b^2) (1/(4096*roundFactor n))

def queryTolerance (n p M : ℕ) (b : ℝ) : ℝ :=
  injection (energyTarget n b) (roundFactor n) M/(roundFactor n*max 1 (((n+1)*p:ℕ):ℝ))

theorem energyTarget_pos (n : ℕ) {b : ℝ} (hb : 0<b) : 0<energyTarget n b := by
  have hC : 0<roundFactor n := lt_of_lt_of_le (by norm_num) (roundFactor_ge_one n)
  exact lt_min (sq_pos_of_pos hb) (by positivity)

theorem energyTarget_le_sq (n : ℕ) (b : ℝ) : energyTarget n b≤b^2 := min_le_left _ _

theorem energyTarget_budget (n : ℕ) (b : ℝ) : roundFactor n*energyTarget n b≤(1:ℝ)/4096 := by
  have hC : 0<roundFactor n := lt_of_lt_of_le (by norm_num) (roundFactor_ge_one n)
  have hh := mul_le_mul_of_nonneg_left (min_le_right (b^2) (1/(4096*roundFactor n))) hC.le
  apply hh.trans_eq
  field_simp
  ring

theorem queryTolerance_pos (n p M : ℕ) {b : ℝ} (hb : 0<b) : 0<queryTolerance n p M b := by
  have hC : 0<roundFactor n := lt_of_lt_of_le (by norm_num) (roundFactor_ge_one n)
  exact div_pos (injection_pos (energyTarget_pos n hb) (roundFactor_ge_one n) M) (by positivity)

theorem injection_le_target {target C : ℝ} (ht : 0≤target) (hC : 1≤C) (M : ℕ) : injection target C M≤target := by
  have hm : (1:ℝ)≤(M:ℝ)+1 := by have hh := Nat.cast_nonneg (α := ℝ) M; linarith
  have hp : (1:ℝ)≤C^(M+1) := one_le_pow₀ hC
  have hd : (1:ℝ)≤((M:ℝ)+1)*C^(M+1) := by nlinarith [mul_le_mul hm hp (by norm_num : (0:ℝ)≤1) (by positivity : (0:ℝ)≤(M:ℝ)+1)]
  exact div_le_self ht hd

theorem queryTolerance_injection (n p M : ℕ) {b : ℝ} (hb : 0<b) :
    roundFactor n*(((n+1)*p:ℕ):ℝ)*queryTolerance n p M b ≤ injection (energyTarget n b) (roundFactor n) M := by
  have hC : 0<roundFactor n := lt_of_lt_of_le (by norm_num) (roundFactor_ge_one n)
  have hQ : (0:ℝ)<max 1 (((n+1)*p:ℕ):ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hi := (injection_pos (energyTarget_pos n hb) (roundFactor_ge_one n) M).le
  dsimp only [queryTolerance]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos hC hQ)).mpr
  have hh := mul_le_mul_of_nonneg_left (le_max_right 1 (((n+1)*p:ℕ):ℝ))
    (mul_nonneg hC.le hi)
  nlinarith

theorem queryTolerance_total_le (n p M : ℕ) {b : ℝ} (hb : 0<b) :
    (((n+1)*p:ℕ):ℝ)*queryTolerance n p M b≤energyTarget n b := by
  have hnon : 0≤(((n+1)*p:ℕ):ℝ)*queryTolerance n p M b := mul_nonneg (Nat.cast_nonneg _) (queryTolerance_pos n p M hb).le
  have hh := mul_le_mul_of_nonneg_right (roundFactor_ge_one n) hnon
  simp only [one_mul,← mul_assoc] at hh
  exact (hh.trans (queryTolerance_injection n p M hb)).trans
    (injection_le_target (energyTarget_pos n hb).le (roundFactor_ge_one n) M)

theorem horizon_step_budget (n p M : ℕ) {b E : ℝ} (hb : 0<b) (hE : E≤energyTarget n b) :
    batchFactor n*(E+(((n+1)*p:ℕ):ℝ)*queryTolerance n p M b)≤(1:ℝ)/4096 := by
  have hsum := add_le_add hE (queryTolerance_total_le n p M hb)
  have hh := mul_le_mul_of_nonneg_left hsum (le_trans (by norm_num) (batchFactor_ge_one n))
  have he : batchFactor n*(energyTarget n b+energyTarget n b)=roundFactor n*energyTarget n b := by
    dsimp [roundFactor]
    ring
  rw [he] at hh
  exact hh.trans (energyTarget_budget n b)

theorem run_energy_horizon {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (M : ℕ) {b : ℝ} (hb : 0<b)
    (hgood : ∀ t<M,¬runFailure hT (queryTolerance n p M b) choose respond memory z t) :
    ∀ t≤M,runEnergy hT choose respond memory z t≤energyTarget n b := by
  apply stopped_energy_bound (runEnergy hT choose respond memory z) (energyTarget_pos n hb).le (roundFactor_ge_one n) M
    (le_of_eq (runEnergy_zero hT hpos choose respond memory z))
  intro t ht hprev
  have hs := run_energy_step hT hn (queryTolerance n p M b) choose respond memory z t
    (horizon_step_budget n p M hb (hprev t le_rfl)) (hgood t ht)
  apply hs.trans
  rw [mul_add]
  exact add_le_add_left (by simpa only [mul_assoc] using queryTolerance_injection n p M hb) _

theorem run_projection_bound {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (M : ℕ) {b : ℝ} (hb : 0<b)
    (hgood : ∀ t<M,¬runFailure hT (queryTolerance n p M b) choose respond memory z t)
    (t : ℕ) (ht : t≤M) (v : Vertex n) (i : Fin T) (hi : ¬Protected t v i) :
    ‖project (known (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t).2 v)
      (frame T hT z v i)‖≤b := by
  classical
  have him : i∈oldFuture T t v := by simpa only [oldFuture,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hrow := TransportRoundEnergy.row_le_total
    (known (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t).2) (frame T hT z) (oldFuture T t) v
  have hsingle := Finset.single_le_sum (fun j (_ : j∈oldFuture T t v) => sq_nonneg
    ‖project (known (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t).2 v) (frame T hT z v j)‖) him
  have hsq := ((hsingle.trans hrow).trans (run_energy_horizon hT hn hpos choose respond memory z M hb hgood t ht)).trans
    (energyTarget_le_sq n b)
  exact (sq_le_sq₀ (norm_nonneg _) hb.le).mp hsq

end Bilevel.TransportRound
