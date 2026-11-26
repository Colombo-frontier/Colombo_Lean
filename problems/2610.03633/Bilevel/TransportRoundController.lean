import Bilevel.TransportRoundBatch

/-! A genuine finite frozen-round execution with a measurable adaptive
memory. Query coordinates and all transport answers are fed to the memory
update. Named disclosures are appended only after that response. The finite
generator/probe bounds depend on the horizon and network, never on ambient
dimension. Restrictions on which named columns are legal are separate. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

abbrev Queries (n D p : ℕ) := Vertex n → Fin p → Space D
abbrev Answers (n p T : ℕ) := Vertex n → Fin p → Fin T → ℝ

def augment {n D m p : ℕ} (g : Generators n D m) (q : Queries n D p) :
    Generators n D (m+p) := fun v => Fin.append (g v) (q v)

theorem augment_measurable (n D m p : ℕ) :
    Measurable (fun z : Generators n D m × Queries n D p => augment z.1 z.2) := by
  apply measurable_pi_lambda
  intro v
  have hg : Measurable (fun z : Generators n D m × Queries n D p => z.1 v) :=
    (measurable_pi_apply v).comp measurable_fst
  have hq : Measurable (fun z : Generators n D m × Queries n D p => z.2 v) :=
    (measurable_pi_apply v).comp measurable_snd
  exact (TransportGeneratorStore.append_measurable D m p).comp (hg.prodMk hq)

theorem augment_span {n D m p : ℕ} (g : Generators n D m) (q : Queries n D p) (v : Vertex n) :
    known (augment g q) v = known g v ⊔ TransportGeneratorStore.span (q v) :=
  TransportGeneratorStore.span_append _ _

def queryAnswers {n D p : ℕ} (T : ℕ) (hT : T ≤ D)
    (q : Queries n D p) (z : Latent n D) : Answers n p T :=
  fun v i j => ⟪q v i,frame T hT z v j⟫

theorem queryAnswers_measurable {n D p : ℕ} (T : ℕ) (hT : T ≤ D) :
    Measurable (fun z : Queries n D p × Latent n D => queryAnswers T hT z.1 z.2) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hq : Measurable (fun z : Queries n D p × Latent n D => z.1 v i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply v).comp measurable_fst)
  have hf : Measurable (fun z : Queries n D p × Latent n D => frame T hT z.2 v j) :=
    ((measurable_pi_apply j).comp ((measurable_pi_apply v).comp (frame_measurable n D T hT))).comp measurable_snd
  exact (continuous_fst.inner continuous_snd).measurable.comp (hq.prodMk hf)

def disclosures {n D c : ℕ} (T : ℕ) (hT : T ≤ D)
    (names : Vertex n → Fin c → Option (Fin T)) (z : Latent n D) : Generators n D c :=
  fun v i => match names v i with | none => 0 | some j => frame T hT z v j

theorem disclosures_measurable {n D c : ℕ} (T : ℕ) (hT : T ≤ D)
    (names : Vertex n → Fin c → Option (Fin T)) : Measurable (disclosures T hT names) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  cases hn : names v i with
  | none => simpa only [disclosures,hn] using (measurable_const : Measurable (fun _ : Latent n D => (0 : Space D)))
  | some j =>
    simpa only [disclosures,hn] using
      ((measurable_pi_apply j).comp ((measurable_pi_apply v).comp (frame_measurable n D T hT)))

def nextSize (n p c m : ℕ) : ℕ := (m+p)+(n*(m+p)+n*(m+p))+c

abbrev StepData (H : Type*) (n D m p T : ℕ) :=
  (H × Generators n D m) × Answers n p T × (Fin (n*(m+p)+n*(m+p)) → Space D)

def round {H : Type*} {n D m p c : ℕ} (T : ℕ) (hT : T ≤ D)
    (choose : H × Generators n D m → Queries n D p)
    (respond : StepData H n D m p T → H)
    (names : Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) : H × Generators n D (nextSize n p c m) :=
  let q := choose s
  let frozen := augment s.2 q
  let y := batch frozen z
  (respond (s,queryAnswers T hT q z,y),augment (outputs frozen y) (disclosures T hT names z))

theorem round_measurable {H : Type*} [MeasurableSpace H] {n D m p c : ℕ}
    (T : ℕ) (hT : T ≤ D) (choose : H × Generators n D m → Queries n D p)
    (hc : Measurable choose) (respond : StepData H n D m p T → H) (hr : Measurable respond)
    (names : Vertex n → Fin c → Option (Fin T)) :
    Measurable (fun z : (H × Generators n D m) × Latent n D => round T hT choose respond names z.1 z.2) := by
  have hq : Measurable (fun z : (H × Generators n D m) × Latent n D => choose z.1) := hc.comp measurable_fst
  have hg : Measurable (fun z : (H × Generators n D m) × Latent n D => augment z.1.2 (choose z.1)) :=
    (augment_measurable n D m p).comp ((measurable_snd.comp measurable_fst).prodMk hq)
  have hy := (batch_joint_measurable n D (m+p)).comp (hg.prodMk measurable_snd)
  have ha := (queryAnswers_measurable (p := p) T hT).comp (hq.prodMk measurable_snd)
  have hout := (outputs_measurable n D (m+p)).comp (hg.prodMk hy)
  exact (hr.comp (measurable_fst.prodMk (ha.prodMk hy))).prodMk
    ((augment_measurable n D ((m+p)+(n*(m+p)+n*(m+p))) c).comp
      (hout.prodMk ((disclosures_measurable T hT names).comp measurable_snd)))

theorem round_dimension {H : Type*} {n D m p c : ℕ} (T : ℕ) (hT : T ≤ D)
    (choose : H × Generators n D m → Queries n D p) (respond : StepData H n D m p T → H)
    (names : Vertex n → Fin c → Option (Fin T)) (s : H × Generators n D m) (z : Latent n D) (v : Vertex n) :
    Module.finrank ℝ (known (round T hT choose respond names s z).2 v) ≤ nextSize n p c m :=
  TransportGeneratorStore.span_rank_le _

def size (n p c m : ℕ) : ℕ → ℕ
  | 0 => m
  | t+1 => nextSize n p c (size n p c m t)

theorem size_bound (n p c m t : ℕ) : size n p c m t+p+c ≤ (m+p+c)*(2*n+2)^t := by
  induction t with
  | zero => simp [size]
  | succ t ih =>
    have hh : nextSize n p c (size n p c m t)+p+c ≤ (2*n+2)*(size n p c m t+p+c) := by
      dsimp [nextSize]
      nlinarith
    calc
      _ ≤ (2*n+2)*(size n p c m t+p+c) := hh
      _ ≤ (2*n+2)*((m+p+c)*(2*n+2)^t) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ring

def run {H : Type*} {n D p c m : ℕ} (T : ℕ) (hT : T ≤ D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) : (t : ℕ) → H × Generators n D (size n p c m t)
  | 0 => s
  | t+1 => round T hT (choose t) (respond t) (names t) (run T hT choose respond names s z t) z

theorem run_measurable {H : Type*} [MeasurableSpace H] {n D p c m : ℕ} (T : ℕ) (hT : T ≤ D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p) (hc : ∀ t, Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H) (hr : ∀ t, Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (t : ℕ) :
    Measurable (fun z : (H × Generators n D m) × Latent n D => run T hT choose respond names z.1 z.2 t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    exact (round_measurable T hT (choose t) (hc t) (respond t) (hr t) (names t)).comp
      (ih.prodMk measurable_snd)

theorem run_dimension {H : Type*} {n D p c m : ℕ} (T : ℕ) (hT : T ≤ D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (t : ℕ) (v : Vertex n) :
    Module.finrank ℝ (known (run T hT choose respond names s z t).2 v) ≤ (m+p+c)*(2*n+2)^t :=
  (TransportGeneratorStore.span_rank_le _).trans ((Nat.le_add_right _ _).trans
    ((Nat.le_add_right _ _).trans (size_bound n p c m t)))

end Bilevel.TransportRound
