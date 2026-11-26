import Bilevel.TransportControllerMachineFrozen

/-! A concrete Borel machine for one actual adaptive frozen round. The full
conditioned context is fixed in memory, the real query answers and entire
batch response are passed to the original response map, and legal named
disclosures are appended in precisely the original order. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

abbrev RoundMemory (H : Memory.{u}) {n : ℕ} (D T m : ℕ) (e : Edge n) : Memory.{u} :=
  Memory.of (Context (d := D) e T × (H × Generators n D m))

theorem contextQueries_measurable {n D T p : ℕ} (e : Edge n) :
    Measurable (fun s : Context (d := D) e T × Queries n D p => contextQueries s.1 s.2) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hq : Measurable (fun s : Context (d := D) e T × Queries n D p => s.2 v i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply v).comp measurable_snd)
  have hf : Measurable (fun s : Context (d := D) e T × Queries n D p => s.1.1 v j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply v).comp (measurable_fst.comp measurable_fst))
  exact (continuous_fst.inner continuous_snd).measurable.comp (hq.prodMk hf)

theorem contextDisclosures_measurable {n D T c : ℕ} (e : Edge n)
    (names : Vertex n → Fin c → Option (Fin T)) :
    Measurable (fun s : Context (d := D) e T => contextDisclosures s names) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  cases he : names v i with
  | none => simpa only [contextDisclosures,he] using
      (measurable_const : Measurable (fun _ : Context (d := D) e T => (0 : Space D)))
  | some j => simpa only [contextDisclosures,he] using
      ((measurable_pi_apply j).comp ((measurable_pi_apply v).comp measurable_fst))

def roundFinish {n D T m p c : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p)
    (respond : StepData H n D m p T → H) (names : Vertex n → Fin c → Option (Fin T))
    (s : RoundMemory H D T m e × (Fin (n*(m+p)+n*(m+p)) → Space D)) :
    RoundMemory H D T (nextSize n p c m) e :=
  let q := choose s.1.2
  let frozen := augment s.1.2.2 q
  (s.1.1,(respond (s.1.2,contextQueries s.1.1 q,s.2),
    augment (outputs frozen s.2) (contextDisclosures s.1.1 names)))

theorem roundFinish_measurable {n D T m p c : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
    (respond : StepData H n D m p T → H) (hr : Measurable respond)
    (names : Vertex n → Fin c → Option (Fin T)) : Measurable (roundFinish H e choose respond names) := by
  have hs : Measurable (fun s : RoundMemory H D T m e × (Fin (n*(m+p)+n*(m+p)) → Space D) => s.1.2) :=
    measurable_snd.comp measurable_fst
  have hctx : Measurable (fun s : RoundMemory H D T m e × (Fin (n*(m+p)+n*(m+p)) → Space D) => s.1.1) :=
    measurable_fst.comp measurable_fst
  have hq := hc.comp hs
  have hg := (augment_measurable n D m p).comp ((measurable_snd.comp hs).prodMk hq)
  have ha := (contextQueries_measurable e).comp (hctx.prodMk hq)
  have ho := (outputs_measurable n D (m+p)).comp (hg.prodMk measurable_snd)
  have hd := (contextDisclosures_measurable e names).comp hctx
  exact hctx.prodMk ((hr.comp (hs.prodMk (ha.prodMk measurable_snd))).prodMk
    ((augment_measurable n D ((m+p)+(n*(m+p)+n*(m+p))) c).comp (ho.prodMk hd)))

def roundMachine {n D T m p c d k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
    (respond : StepData H n D m p T → H) (hr : Measurable respond)
    (names : Vertex n → Fin c → Option (Fin T)) :
    Machine D d (RoundMemory H D T (nextSize n p c m) e) (bothCount k (m+p))
      (RoundMemory H D T m e) k ((m+p)+(m+p)) := by
  let g : RoundMemory H D T m e → Generators n D (m+p) := fun s => augment s.2.2 (choose s.2)
  have hg : Measurable g := (augment_measurable n D m p).comp
    ((measurable_snd.comp measurable_snd).prodMk (hc.comp measurable_snd))
  exact map (C := RoundMemory H D T (nextSize n p c m) e)
    (contextBatch (d := d) (m := k) (RoundMemory H D T m e) e Prod.fst measurable_fst g hg)
    (roundFinish H e choose respond names) (roundFinish_measurable H e choose hc respond hr names)

theorem roundMachine_memory {n D T m p c d k : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
    (respond : StepData H n D m p T → H) (hr : Measurable respond)
    (names : Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m)
    (L : TransportControllerPairedStore.State D k) (z : Latent n D) :
    (value (roundMachine (d := d) H e choose hc respond hr names) ((context T hT e z,st),L) (z.2 e)).1=
      (context T hT e z,round T hT choose respond names st z) := by
  simp only [roundMachine,value_map]
  rw [contextBatch_memory _ hT _ _ _ _ _ _ z rfl]
  rfl

theorem roundMachine_no_failure {n D T m p c d k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
    (respond : StepData H n D m p T → H) (hr : Measurable respond)
    (names : Vertex n → Fin c → Option (Fin T)) (s : State (RoundMemory H D T m e) D k)
    (O : OrthogonalHaar.Group D) :
    ¬failure (roundMachine (d := d) H e choose hc respond hr names) s O := by
  simp only [roundMachine,failure_map]
  exact contextBatch_no_failure _ _ _ _ _ _ _ _

end Bilevel.TransportControllerMachine
