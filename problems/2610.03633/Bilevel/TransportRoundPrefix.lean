import Bilevel.TransportRoundController

/-! The actual one-column-per-stage disclosure schedule. Column i is a
protected named column at layer v only after i*n+v completed rounds. The next
source column is appended after the round response, and transported only in
later frozen batches. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction
set_option maxHeartbeats 600000

def prefixNames (n T t : ℕ) : Vertex n → Fin 1 → Option (Fin T) := fun v _ =>
  if v=0 ∧ (t+1)%n=0 then if h : (t+1)/n<T then some ⟨(t+1)/n,h⟩ else none else none

def seed {n D : ℕ} (T : ℕ) (hT : T ≤ D) (z : Latent n D) : Generators n D 1 := fun v _ =>
  if v=0 then if h : 0<T then frame T hT z 0 ⟨0,h⟩ else 0 else 0

theorem seed_measurable {n D : ℕ} (T : ℕ) (hT : T ≤ D) : Measurable (seed (n := n) T hT) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  by_cases hv : v=0
  · subst v
    by_cases h : 0<T
    · simpa only [seed,ite_true,dif_pos h] using named_measurable T hT (0 : Vertex n) ⟨0,h⟩
    · simp only [seed,ite_true,dif_neg h]
      exact measurable_const
  · simp only [seed,if_neg hv]
    exact measurable_const

def Protected {n T : ℕ} (t : ℕ) (v : Vertex n) (i : Fin T) : Prop := i.val*n+v.val ≤ t

theorem seed_protected {n D : ℕ} (T : ℕ) (hT : T ≤ D) (hn : 0<n) (z : Latent n D)
    (v : Vertex n) (i : Fin T) (hi : Protected 0 v i) : frame T hT z v i ∈ known (seed T hT z) v := by
  have hv : v=0 := Fin.ext (by change v.val=0; dsimp [Protected] at hi; omega)
  have hi0 : i.val=0 := by dsimp [Protected] at hi; nlinarith
  subst v
  have hT0 : 0<T := by omega
  have he : i = (⟨0,hT0⟩ : Fin T) := Fin.ext hi0
  have hh := TransportGeneratorStore.generator_mem (seed T hT z (0 : Vertex n)) (0 : Fin 1)
  simpa only [seed,ite_true,dif_pos hT0,he] using hh

theorem round_keeps {H : Type*} {n D m p c : ℕ} (T : ℕ) (hT : T ≤ D)
    (choose : H × Generators n D m → Queries n D p) (respond : StepData H n D m p T → H)
    (names : Vertex n → Fin c → Option (Fin T)) (s : H × Generators n D m) (z : Latent n D) (v : Vertex n) :
    known s.2 v ≤ known (round T hT choose respond names s z).2 v := by
  change known s.2 v ≤ known (augment (execute (augment s.2 (choose s)) z) (disclosures T hT names z)) v
  rw [augment_span]
  apply le_trans _ le_sup_left
  apply le_trans _ (keeps_old (augment s.2 (choose s)) z v)
  rw [augment_span]
  exact le_sup_left

theorem round_forward {H : Type*} {n D m p c : ℕ} (T : ℕ) (hT : T ≤ D)
    (choose : H × Generators n D m → Queries n D p) (respond : StepData H n D m p T → H)
    (names : Vertex n → Fin c → Option (Fin T)) (s : H × Generators n D m) (z : Latent n D) (e : Edge n)
    (x : Space D) (hx : x ∈ known s.2 (src e)) :
    z.2 e • x ∈ known (round T hT choose respond names s z).2 (dst e) := by
  change z.2 e • x ∈ known (augment (execute (augment s.2 (choose s)) z) (disclosures T hT names z)) (dst e)
  rw [augment_span]
  apply (show known (execute (augment s.2 (choose s)) z) (dst e) ≤ _ from le_sup_left)
  apply forward_whole_space (augment s.2 (choose s)) z e
  refine ⟨x,?_,rfl⟩
  rw [augment_span]
  exact (show known s.2 (src e) ≤ _ from le_sup_left) hx

theorem round_prefix {H : Type*} {n D m p : ℕ} (T : ℕ) (hT : T ≤ D) (hn : 0<n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p) (respond : StepData H n D m p T → H)
    (s : H × Generators n D m) (z : Latent n D)
    (hs : ∀ v i, Protected t v i → frame T hT z v i ∈ known s.2 v) :
    ∀ v i, Protected (t+1) v i →
      frame T hT z v i ∈ known (round T hT choose respond (prefixNames n T t) s z).2 v := by
  intro v i hi
  cases v using Fin.cases with
  | zero =>
    by_cases hiold : i.val*n ≤ t
    · exact round_keeps T hT choose respond _ s z 0 (hs 0 i (by exact hiold))
    · have hieq : i.val*n=t+1 := by dsimp [Protected] at hi; omega
      have hdiv : (t+1)/n=i.val := by rw [← hieq,Nat.mul_div_left _ hn]
      have hmod : (t+1)%n=0 := by rw [← hieq]; simp
      have hTi : (t+1)/n<T := by rw [hdiv]; exact i.isLt
      have he : i=(⟨(t+1)/n,hTi⟩ : Fin T) := Fin.ext hdiv.symm
      change frame T hT z 0 i ∈ known (augment _ (disclosures T hT (prefixNames n T t) z)) 0
      rw [augment_span]
      apply (show TransportGeneratorStore.span (disclosures T hT (prefixNames n T t) z 0) ≤ _ from le_sup_right)
      have hh := TransportGeneratorStore.generator_mem (disclosures T hT (prefixNames n T t) z 0) (0 : Fin 1)
      simpa only [disclosures,prefixNames,hmod,and_self,ite_true,dif_pos hTi,he] using hh
  | succ v =>
    have hp : Protected t (src v) i := by dsimp [Protected,src] at hi ⊢; omega
    have hh := round_forward T hT choose respond (prefixNames n T t) s z v _ (hs (src v) i hp)
    simpa only [edge_frame] using hh

theorem run_prefix {H : Type*} {n D p : ℕ} (T : ℕ) (hT : T ≤ D) (hn : 0<n)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H)
    (h : H) (z : Latent n D) (t : ℕ) :
    ∀ v i, Protected t v i →
      frame T hT z v i ∈ known (run T hT choose respond (prefixNames n T) (h,seed T hT z) z t).2 v := by
  induction t with
  | zero => exact seed_protected T hT hn z
  | succ t ih => exact round_prefix T hT hn t (choose t) (respond t) _ z ih

theorem future_not_protected {n T : ℕ} (t : ℕ) (i : Fin T) (hi : t < i.val*n) (v : Vertex n) :
    ¬ Protected t v i := by dsimp [Protected]; omega

theorem completed_prefix {n T : ℕ} (hn : 0<n) (t : ℕ) (i : Fin T) :
    Protected t (Fin.last n) i ↔ i.val+1 ≤ t/n := by
  rw [Nat.le_div_iff_mul_le hn]
  change i.val*n+n ≤ t ↔ (i.val+1)*n ≤ t
  rw [Nat.add_mul,one_mul]

end Bilevel.TransportRound
