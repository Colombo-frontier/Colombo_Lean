import Bilevel.TransportRoundReverseLedger

/-! The genuine simultaneous frozen transport batch has a derived finite
energy recurrence on its explicitly defined fresh-monitor event. The scalar
budget discharges all intermediate protected-angle smallness requirements.
The probability of this same-run event remains a separate compiler bridge. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior
set_option maxHeartbeats 800000

def batchFactor (n : ℕ) : ℝ := 3*9^n*17^n

theorem batchFactor_ge_one (n : ℕ) : 1≤batchFactor n := by
  have h9 : (1:ℝ)≤9^n := one_le_pow₀ (by norm_num)
  have h17 : (1:ℝ)≤17^n := one_le_pow₀ (by norm_num)
  dsimp [batchFactor]
  nlinarith [mul_le_mul h9 h17 (by norm_num : (0:ℝ)≤1) (by positivity : (0:ℝ)≤9^n)]

def batchFailure {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D)
    (P : Edge n → Pairs D) : Prop :=
  forwardFailure hT t g z P (List.ofFn (fun e : Edge n => e)) (known (postGrant T hT t g z)) ∨
    reverseFailure hT t g z P (List.ofFn (fun e : Edge n => e))
      (forwardLedger g z (known (postGrant T hT t g z)))

theorem executed_batch_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D)
    (hP : ∀ e,Supports (P e) (z.2 e))
    (hPS : ∀ e,domain (P e)≤known g (src e)) (hPD : ∀ e,range (P e)≤known g (dst e))
    (hprefix : ∀ v i,Protected t v i→frame T hT z v i∈known g v)
    (hbudget : batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)≤(1:ℝ)/4096)
    (hgood : ¬batchFailure hT t g z P) :
    TransportRoundEnergy.total (known (execute g z)) (frame T hT z) (postFuture T t) ≤
      batchFactor n*TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) := by
  let B := TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)
  let G := known (postGrant T hT t g z)
  let F := forwardLedger g z G
  have hB : 0≤B := TransportRoundEnergy.total_nonneg _ _ _
  have hsmall : B≤(1:ℝ)/4096 := by
    have hm := mul_le_mul_of_nonneg_right (batchFactor_ge_one n) hB
    simp only [one_mul] at hm
    exact hm.trans hbudget
  have hgrant := postGrant_total_energy T hT hn t g z hsmall
  have hg := not_or.mp hgood
  have hf := forwardAlong_energy hT hn t g z P hP hPS hPD hprefix
    (List.ofFn (fun e : Edge n => e)) G (fun _ => le_rfl) hsmall hg.1
  rw [forwardAlong_all,List.length_ofFn] at hf
  have hF : TransportRoundEnergy.total F (frame T hT z) (postFuture T t)≤3*9^n*B := by
    have hh := mul_le_mul_of_nonneg_left hgrant (by positivity : (0:ℝ)≤9^n)
    change _+B≤9^n*(_+B) at hf
    dsimp only [F,G]
    change _≤3*9^n*B
    nlinarith
  have hFbudget : 17^(List.ofFn (fun e : Edge n => e)).length*
      TransportRoundEnergy.total F (frame T hT z) (postFuture T t)≤(1:ℝ)/4096 := by
    rw [List.length_ofFn]
    apply (mul_le_mul_of_nonneg_left hF (by positivity)).trans
    convert hbudget using 1
    dsimp [batchFactor,B]
    ring
  have hr := reverseAlong_energy hT hn t g z P hP hPS hPD hprefix
    (List.ofFn (fun e : Edge n => e)) F (fun _ => le_rfl) hFbudget hg.2
  rw [reverseAlong_all,List.length_ofFn] at hr
  have he : reverseLedger g z F=known (execute g z) := granted_ledgers_eq_execute hT t g z hprefix
  rw [he] at hr
  apply hr.trans
  have hh := mul_le_mul_of_nonneg_left hF (by positivity : (0:ℝ)≤17^n)
  convert hh using 1
  dsimp [batchFactor,B]
  ring

end Bilevel.TransportRound
