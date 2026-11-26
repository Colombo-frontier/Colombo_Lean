import Bilevel.TransportRoundRunProbability

/-! Pre-transport projection control includes every current raw query
vector. The tracked future set is the old prefix, so the newly crossing
column is still controlled before this batch and its later disclosure. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork ProjectionGeometry
set_option maxHeartbeats 800000

theorem frozen_energy_horizon {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (M : ℕ) {b : ℝ} (hb : 0<b)
    (hgood : ∀ t<M,¬runFailure hT (queryTolerance n p M b) choose respond memory z t) (t : ℕ) (ht : t<M) :
    TransportRoundEnergy.total (known (frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t))
      (frame T hT z) (oldFuture T t)≤2*energyTarget n b := by
  let st := run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t
  have hq := frozen_query_energy hT (queryTolerance n p M b) st.2 (choose t st) z (oldFuture T t) (not_or.mp (hgood t ht)).1
  have he := run_energy_horizon hT hn hpos choose respond memory z M hb hgood t ht.le
  have hi := queryTolerance_total_le n p M hb
  apply hq.trans
  change runEnergy hT choose respond memory z t+_≤_
  linarith

theorem frozen_projection_bound {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (M : ℕ) {b : ℝ} (hb : 0<b)
    (hgood : ∀ t<M,¬runFailure hT (queryTolerance n p M b) choose respond memory z t)
    (t : ℕ) (ht : t<M) (v : Vertex n) (i : Fin T) (hi : ¬Protected t v i) :
    ‖project (known (frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t) v) (frame T hT z v i)‖≤2*b := by
  classical
  let W := known (frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t)
  have him : i∈oldFuture T t v := by simpa only [oldFuture,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hrow := TransportRoundEnergy.row_le_total W (frame T hT z) (oldFuture T t) v
  have hsingle := Finset.single_le_sum (fun j (_ : j∈oldFuture T t v) => sq_nonneg ‖project (W v) (frame T hT z v j)‖) him
  have hsq := (hsingle.trans hrow).trans (frozen_energy_horizon hT hn hpos choose respond memory z M hb hgood t ht)
  have hb2 := energyTarget_le_sq n b
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : (0:ℝ)≤2*b)).mp
  nlinarith

def ProjectionGood {H : Type*} {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (M : ℕ) (b : ℝ) (memory : H) (z : Latent n D) : Prop :=
  (∀ t≤M,∀ v i,¬Protected t v i →
    ‖project (known (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t).2 v) (frame T hT z v i)‖≤b) ∧
  (∀ t<M,∀ v i,¬Protected t v i →
    ‖project (known (frozenAt hT choose respond (prefixNames n T) (memory,seed T hT z) z t) v) (frame T hT z v i)‖≤b)

theorem projectionGood_of_no_failure {H : Type*} {n D p T : ℕ} (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (M : ℕ) {b : ℝ} (hb : 0<b)
    (hgood : ∀ t<M,¬runFailure hT (queryTolerance n p M (b/2)) choose respond memory z t) :
    ProjectionGood hT choose respond M b memory z := by
  have hh : 0<b/2 := by positivity
  constructor
  · intro t ht v i hi
    exact (run_projection_bound hT hn hpos choose respond memory z M hh hgood t ht v i hi).trans (by linarith)
  · intro t ht v i hi
    have h := frozen_projection_bound hT hn hpos choose respond memory z M hh hgood t ht v i hi
    nlinarith

end Bilevel.TransportRound
