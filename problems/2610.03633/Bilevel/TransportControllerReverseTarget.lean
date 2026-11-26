import Bilevel.TransportControllerMachineForwardCheck
import Bilevel.TransportControllerMachineInverseReplay

/-! A finite enlarged reverse target built from the actual frozen forward
responses. It contains the phase's target ledger and has a generator count
independent of ambient dimension. The enlargement is only for a conservative
angle bound; the real controller and energy ledger are unchanged. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound TransportGeneratorStore
set_option maxHeartbeats 800000

def allForward {n D b : ℕ} (g : Generators n D b) (z : Latent n D) : Fin (n*b) → Space D :=
  fun i => batch g z (Fin.castAdd (n*b) i)

theorem forwardImage_le_allForward {n D b : ℕ} (g : Generators n D b) (z : Latent n D) (e : Edge n) :
    (known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap≤span (allForward g z) := by
  rw [known,← transported_span]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  apply Submodule.subset_span
  refine ⟨finProdFinEquiv (e,i),?_⟩
  simp only [allForward,batch,batchObservation,probes,Fin.append_left,forwardProbes,
    Equiv.symm_apply_apply,probeObservation,Bool.false_eq_true,ite_false,forwardObservation]
  rfl

theorem forwardLedger_le_allForward {n D b : ℕ} (g : Generators n D b) (z : Latent n D) (W : Known n D) :
    ∀ v,forwardLedger g z W v≤W v⊔span (allForward g z) := by
  apply mergeBlocks_le (forwardBlocks g z) W (fun v => W v⊔span (allForward g z)) (fun _ => le_sup_left)
  intro b hb
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  exact (forwardImage_le_allForward g z e).trans le_sup_right

def reconstructForward {n D T b : ℕ} (e : Edge n) (ctx : Context (d := D) e T)
    (g : Generators n D b) (yf : Fin b → Space D) : Fin (n*b) → Space D :=
  fun i => reconstructBatch e ctx g yf (fun _ => 0) (Fin.castAdd (n*b) i)

theorem reconstructForward_measurable {n D T b : ℕ} (e : Edge n) :
    Measurable (fun p : (Context (d := D) e T × Generators n D b) × (Fin b → Space D) =>
      reconstructForward e p.1.1 p.1.2 p.2) := by
  have ha : Measurable (fun p : (Context (d := D) e T × Generators n D b) × (Fin b → Space D) =>
      (p.1,(p.2,fun _ : Fin b => (0 : Space D)))) := measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have hh := (reconstructBatch_measurable (D := D) (T := T) (b := b) e).comp ha
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (Fin.castAdd (n*b) i)).comp hh

theorem reconstructForward_correct {n D T b : ℕ} (hT : T≤D) (e : Edge n) (g : Generators n D b) (z : Latent n D) :
    reconstructForward e (context T hT e z) g (batchResponse false (g (src e)) (z.2 e))=allForward g z := by
  funext i
  have hh := congrFun (reconstructBatch_correct hT e g z) (Fin.castAdd (n*b) i)
  simpa only [reconstructForward,allForward,reconstructBatch,Fin.append_left] using hh

def reverseTarget {n D T m p : ℕ} (H : Memory.{u}) (e : Edge n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p)
    (s : RoundMemory H D T m e × (Fin (m+p) → Space D)) : Fin (((m+p)+1)+n*(m+p)) → Space D :=
  Fin.append (grantMemory H e t choose s.1 (src e))
    (reconstructForward e s.1.1 (frozenMemory H e choose s.1) s.2)

theorem reverseTarget_measurable {n D T m p : ℕ} (H : Memory.{u}) (e : Edge n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose) :
    Measurable (reverseTarget (T := T) H e t choose) := by
  have hgrant : Measurable (fun s : RoundMemory H D T m e × (Fin (m+p) → Space D) =>
      grantMemory H e t choose s.1 (src e)) :=
    ((measurable_pi_apply (src e)).comp (grantMemory_measurable H e t choose hc)).comp measurable_fst
  have hargs : Measurable (fun s : RoundMemory H D T m e × (Fin (m+p) → Space D) =>
      ((s.1.1,frozenMemory H e choose s.1),s.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk ((frozenMemory_measurable H e choose hc).comp measurable_fst)).prodMk measurable_snd
  have hy := (reconstructForward_measurable (D := D) (T := T) (b := m+p) e).comp hargs
  exact (append_measurable D ((m+p)+1) (n*(m+p))).comp (hgrant.prodMk hy)

theorem reverseTarget_contains {n D T m p : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p) (st : H × Generators n D m) (z : Latent n D) :
    forwardLedger (augment st.2 (choose st)) z (known (postGrant T hT t (augment st.2 (choose st)) z)) (src e)≤
      span (reverseTarget H e t choose ((context T hT e z,st),
        batchResponse false ((augment st.2 (choose st)) (src e)) (z.2 e))) := by
  rw [reverseTarget,span_append]
  change _≤known (postGrant T hT t (augment st.2 (choose st)) z) (src e)⊔
    span (reconstructForward e (context T hT e z) (augment st.2 (choose st))
      (batchResponse false ((augment st.2 (choose st)) (src e)) (z.2 e)))
  rw [reconstructForward_correct]
  exact forwardLedger_le_allForward _ _ _ _

theorem angleBad_target_mono {D : ℕ} {W V R : Submodule ℝ (Space D)} (h : W≤V) (O : OrthogonalHaar.Group D) :
    TransportControllerEdge.angleBad W R O → TransportControllerEdge.angleBad V R O := by
  rintro ⟨u,hu⟩
  exact ⟨u,hu.trans_le (TransportObserver.project_norm_mono h _)⟩

end Bilevel.TransportControllerMachine
