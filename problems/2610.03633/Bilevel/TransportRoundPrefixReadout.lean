import Bilevel.TransportRoundPrefix

/-! Actual disclosed network columns are Borel readouts of the finite
stored generator array. Membership in its span is not substituted for
availability of a vector in the virtual reply. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction
set_option maxHeartbeats 700000
open Classical

def oldSlot (n p m : ℕ) (i : Fin m) : Fin (nextSize n p 1 m) :=
  Fin.castAdd 1 (Fin.castAdd (n*(m+p)+n*(m+p)) (Fin.castAdd p i))

def forwardSlot (n p m : ℕ) (e : Edge n) (i : Fin m) : Fin (nextSize n p 1 m) :=
  Fin.castAdd 1 (Fin.natAdd (m+p) (Fin.castAdd (n*(m+p))
    (finProdFinEquiv (e,Fin.castAdd p i))))

def disclosureSlot (n p m : ℕ) : Fin (nextSize n p 1 m) :=
  Fin.natAdd ((m+p)+(n*(m+p)+n*(m+p))) (0 : Fin 1)

def protectedSlot {n T : ℕ} (hn : 0<n) (p : ℕ) :
    (t : ℕ) → (v : Vertex n) → (i : Fin T) → Protected t v i → Fin (size n p 1 1 t)
  | 0,_,_,_ => ⟨0,by simp [size]⟩
  | t+1,v,i,hi =>
    if ho : Protected t v i then oldSlot n p _ (protectedSlot hn p t v i ho)
    else Fin.cases (fun _ => disclosureSlot n p _)
      (fun e h => forwardSlot n p _ e (protectedSlot hn p t (src e) i (by
        change i.val*n+e.val≤t
        change i.val*n+e.val+1≤t+1 at h
        omega))) v hi

theorem round_oldSlot {H : Type*} {n D m p : ℕ} (T : ℕ) (hT : T≤D)
    (choose : H × Generators n D m → Queries n D p)
    (respond : StepData H n D m p T → H) (names : Vertex n → Fin 1 → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (v : Vertex n) (i : Fin m) :
    (round T hT choose respond names s z).2 v (oldSlot n p m i)=s.2 v i := by
  simp only [round,oldSlot,augment,outputs,appendOutputs,Fin.append_left]

theorem round_forwardSlot {H : Type*} {n D m p : ℕ} (T : ℕ) (hT : T≤D)
    (choose : H × Generators n D m → Queries n D p)
    (respond : StepData H n D m p T → H) (names : Vertex n → Fin 1 → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (e : Edge n) (i : Fin m) :
    (round T hT choose respond names s z).2 (dst e) (forwardSlot n p m e i)=z.2 e • s.2 (src e) i := by
  simp only [round,forwardSlot,augment,outputs,appendOutputs,Fin.append_left,Fin.append_right,
    probes,forwardProbes,Equiv.symm_apply_apply,outputLayer,Bool.false_eq_true,ite_false,ite_true,
    batch,batchObservation,probeObservation,forwardObservation]

theorem round_disclosureSlot {H : Type*} {n D m p : ℕ} (T : ℕ) (hT : T≤D)
    (choose : H × Generators n D m → Queries n D p)
    (respond : StepData H n D m p T → H) (names : Vertex n → Fin 1 → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (v : Vertex n) (i : Fin T)
    (hi : names v 0=some i) :
    (round T hT choose respond names s z).2 v (disclosureSlot n p m)=frame T hT z v i := by
  simp only [round,disclosureSlot,augment,Fin.append_right,disclosures,hi]

theorem protectedSlot_correct {H : Type*} {n D p : ℕ} (T : ℕ) (hT : T≤D) (hn : 0<n)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) (v : Vertex n) (i : Fin T) (hi : Protected t v i) :
    (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t).2 v (protectedSlot hn p t v i hi)=frame T hT z v i := by
  induction t generalizing v with
  | zero =>
    have hv : v=0 := Fin.ext (by change v.val=0;dsimp [Protected] at hi;omega)
    have hi0 : i.val=0 := by dsimp [Protected] at hi;nlinarith
    subst v
    have hpos : 0<T := i.pos
    have he : i=(⟨0,hpos⟩ : Fin T) := Fin.ext hi0
    simp only [run,protectedSlot,seed,ite_true,dif_pos hpos,he]
  | succ t ih =>
    by_cases ho : Protected t v i
    · simp only [protectedSlot,dif_pos ho,run]
      rw [round_oldSlot]
      exact ih v ho
    · simp only [protectedSlot,dif_neg ho,run]
      cases v using Fin.cases with
      | zero =>
        apply round_disclosureSlot
        have hieq : i.val*n=t+1 := by dsimp [Protected] at hi ho;omega
        have hdiv : (t+1)/n=i.val := by rw [←hieq,Nat.mul_div_left _ hn]
        have hmod : (t+1)%n=0 := by rw [←hieq];simp
        have hTi : (t+1)/n<T := by rw [hdiv];exact i.isLt
        simp only [prefixNames,hmod,and_self,ite_true,dif_pos hTi]
        congr 1
        exact Fin.ext hdiv
      | succ e =>
        simp only [Fin.cases_succ]
        change (round T hT (choose t) (respond t) (prefixNames n T t)
          (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t) z).2
          (dst e) (forwardSlot n p _ e _) = _
        rw [round_forwardSlot,ih]
        exact edge_frame T hT z e i

def prefixReadout {n D T : ℕ} (hn : 0<n) (p t : ℕ)
    (g : Generators n D (size n p 1 1 t)) (v : Vertex n) (i : Fin T) : Space D :=
  if hi : Protected t v i then g v (protectedSlot hn p t v i hi) else 0

theorem prefixReadout_measurable {n D T : ℕ} (hn : 0<n) (p t : ℕ) :
    Measurable (prefixReadout (D:=D) (T:=T) hn p t) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  by_cases hi : Protected t v i
  · simp only [prefixReadout,dif_pos hi]
    exact (measurable_pi_apply _).comp (measurable_pi_apply v)
  · simp only [prefixReadout,dif_neg hi]
    exact measurable_const

theorem prefixReadout_actual {H : Type*} {n D p : ℕ} (T : ℕ) (hT : T≤D) (hn : 0<n)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H)
    (memory : H) (z : Latent n D) (t : ℕ) (v : Vertex n) (i : Fin T) :
    prefixReadout hn p t (run T hT choose respond (prefixNames n T) (memory,seed T hT z) z t).2 v i=
      if Protected t v i then frame T hT z v i else 0 := by
  by_cases hi : Protected t v i
  · simp only [prefixReadout,dif_pos hi,if_pos hi]
    exact protectedSlot_correct T hT hn choose respond memory z t v i hi
  · simp only [prefixReadout,dif_neg hi,if_neg hi]

end Bilevel.TransportRound



