import Bilevel.TransportControllerMachineBatch
import Bilevel.TransportControllerReconstruction

/-! A Borel reconstruction of the genuine simultaneous frozen network batch.
The current edge's forward and reverse responses use the same map, with both
input arrays fixed before the first response. Other edges are read only from
the conditioned context. The physical paired store is never reset. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def bothCount (m b : ℕ) : ℕ := afterCount (afterCount m b) b

theorem bothCount_eq (m b : ℕ) : bothCount m b=m+2*b := by
  simp only [bothCount,afterCount_eq]
  omega

def bidirectional {D d b m : ℕ} (H : Memory.{u})
    (qf qr : H → Fin b → Space D) (hf : Measurable qf) (hr : Measurable qr) :
    Machine D d (Memory.of ((H × (Fin b → Space D)) × (Fin b → Space D))) (bothCount m b) H m (b+b) :=
  compose (collect false b m H qf hf)
    (collect true b (afterCount m b) (Memory.of (H × (Fin b → Space D)))
      (fun s => qr s.1) (hr.comp measurable_fst))

theorem bidirectional_value {D d b m : ℕ} (H : Memory.{u})
    (qf qr : H → Fin b → Space D) (hf : Measurable qf) (hr : Measurable qr)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    value (bidirectional (d := d) H qf qr hf hr) s O =
      (((s.1,batchResponse false (qf s.1) O),batchResponse true (qr s.1) O),
        insertMany true (insertMany false s.2 (qf s.1) (batchResponse false (qf s.1) O))
          (qr s.1) (batchResponse true (qr s.1) O)) := by
  rw [bidirectional,value_compose,collect_value,collect_value]

theorem bidirectional_no_failure {D d b m : ℕ} (H : Memory.{u})
    (qf qr : H → Fin b → Space D) (hf : Measurable qf) (hr : Measurable qr)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    ¬failure (bidirectional (d := d) H qf qr hf hr) s O := by
  rw [bidirectional,failure_compose]
  exact not_or.mpr ⟨collect_no_failure _ _ _ _ _ _,collect_no_failure _ _ _ _ _ _⟩

def reconstructBatch {n D T b : ℕ} (e : Edge n) (c : Context (d := D) e T)
    (g : Generators n D b) (yf yr : Fin b → Space D) : Fin (n*b+n*b) → Space D :=
  Fin.append
    (fun j => let ei : Edge n × Fin b := finProdFinEquiv.symm j
      if h : ei.1=e then yf ei.2 else c.2 ⟨ei.1,h⟩ • g (src ei.1) ei.2)
    (fun j => let ei : Edge n × Fin b := finProdFinEquiv.symm j
      if h : ei.1=e then yr ei.2 else (c.2 ⟨ei.1,h⟩)⁻¹ • g (dst ei.1) ei.2)

theorem reconstructBatch_measurable {n D T b : ℕ} (e : Edge n) :
    Measurable (fun p : (Context (d := D) e T × Generators n D b) ×
      (Fin b → Space D) × (Fin b → Space D) => reconstructBatch e p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    let ei : Edge n × Fin b := finProdFinEquiv.symm j
    by_cases he : (finProdFinEquiv.symm j : Edge n × Fin b).1=e
    · simp only [reconstructBatch,Fin.append_left,he,dif_pos]
      exact (measurable_pi_apply ei.2).comp (measurable_fst.comp measurable_snd)
    · simp only [reconstructBatch,Fin.append_left,he,dif_neg]
      exact ((measurable_pi_apply (⟨ei.1,he⟩ : {e' : Edge n // e'≠e})).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).smul
        ((measurable_pi_apply ei.2).comp ((measurable_pi_apply (src ei.1)).comp (measurable_snd.comp measurable_fst)))
  · intro j
    let ei : Edge n × Fin b := finProdFinEquiv.symm j
    by_cases he : (finProdFinEquiv.symm j : Edge n × Fin b).1=e
    · simp only [reconstructBatch,Fin.append_right,he,dif_pos]
      exact (measurable_pi_apply ei.2).comp (measurable_snd.comp measurable_snd)
    · simp only [reconstructBatch,Fin.append_right,he,dif_neg]
      exact (((measurable_pi_apply (⟨ei.1,he⟩ : {e' : Edge n // e'≠e})).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).inv).smul
        ((measurable_pi_apply ei.2).comp ((measurable_pi_apply (dst ei.1)).comp (measurable_snd.comp measurable_fst)))

theorem reconstructBatch_correct {n D T b : ℕ} (hT : T≤D) (e : Edge n) (g : Generators n D b) (z : Latent n D) :
    reconstructBatch e (context T hT e z) g
      (batchResponse false (g (src e)) (z.2 e)) (batchResponse true (g (dst e)) (z.2 e))=batch g z := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    let ei : Edge n × Fin b := finProdFinEquiv.symm j
    simp only [reconstructBatch,Fin.append_left,batch,batchObservation,probes,Fin.append_left,
      forwardProbes,probeObservation,Bool.false_eq_true,ite_false,forwardObservation]
    change (if h : ei.1=e then batchResponse false (g (src e)) (z.2 e) ei.2
      else (context T hT e z).2 ⟨ei.1,h⟩ • g (src ei.1) ei.2)=z.2 ei.1 • g (src ei.1) ei.2
    by_cases he : ei.1=e
    · simp only [he,dif_pos,batchResponse,Bool.false_eq_true,ite_false]
    · rw [dif_neg he]; rfl
  · intro j
    let ei : Edge n × Fin b := finProdFinEquiv.symm j
    simp only [reconstructBatch,Fin.append_right,batch,batchObservation,probes,Fin.append_right,
      reverseProbes,probeObservation,ite_true,reverseObservation]
    change (if h : ei.1=e then batchResponse true (g (dst e)) (z.2 e) ei.2
      else ((context T hT e z).2 ⟨ei.1,h⟩)⁻¹ • g (dst ei.1) ei.2)=(z.2 ei.1)⁻¹ • g (dst ei.1) ei.2
    by_cases he : ei.1=e
    · simp only [he,dif_pos,batchResponse,ite_true]
    · rw [dif_neg he]; rfl

def contextFinish {H : Type*} {n D T b : ℕ} (e : Edge n)
    (ctx : H → Context (d := D) e T) (g : H → Generators n D b)
    (p : (H × (Fin b → Space D)) × (Fin b → Space D)) : H × (Fin (n*b+n*b) → Space D) :=
  (p.1.1,reconstructBatch e (ctx p.1.1) (g p.1.1) p.1.2 p.2)

theorem contextFinish_measurable {H : Type*} [MeasurableSpace H] {n D T b : ℕ} (e : Edge n)
    (ctx : H → Context (d := D) e T) (hc : Measurable ctx)
    (g : H → Generators n D b) (hg : Measurable g) : Measurable (contextFinish e ctx g) := by
  let A := (H × (Fin b → Space D)) × (Fin b → Space D)
  have hmem : Measurable (fun p : A => p.1.1) := measurable_fst.comp measurable_fst
  have hargs : Measurable (fun p : A => ((ctx p.1.1,g p.1.1),(p.1.2,p.2))) :=
    ((hc.comp hmem).prodMk (hg.comp hmem)).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hout := (reconstructBatch_measurable (D := D) (T := T) (b := b) e).comp hargs
  apply Measurable.prodMk
  · exact hmem
  · exact hout

def contextBatch {n D T b d m : ℕ} (H : Memory.{u}) (e : Edge n)
    (ctx : H → Context (d := D) e T) (hc : Measurable ctx)
    (g : H → Generators n D b) (hg : Measurable g) :
    Machine D d (Memory.of (H × (Fin (n*b+n*b) → Space D))) (bothCount m b) H m (b+b) := by
  let qf : H → Fin b → Space D := fun s => g s (src e)
  let qr : H → Fin b → Space D := fun s => g s (dst e)
  have hf : Measurable qf := (measurable_pi_apply (src e)).comp hg
  have hr : Measurable qr := (measurable_pi_apply (dst e)).comp hg
  exact map (C := Memory.of (H × (Fin (n*b+n*b) → Space D))) (bidirectional (d := d) (m := m) H qf qr hf hr)
    (contextFinish e ctx g) (contextFinish_measurable e ctx hc g hg)

theorem contextBatch_memory {n D T b d m : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (ctx : H → Context (d := D) e T) (hc : Measurable ctx)
    (g : H → Generators n D b) (hg : Measurable g)
    (s : State H D m) (z : Latent n D) (he : ctx s.1=context T hT e z) :
    (value (contextBatch (d := d) H e ctx hc g hg) s (z.2 e)).1=(s.1,batch (g s.1) z) := by
  simp only [contextBatch,value_map,bidirectional_value,contextFinish]
  rw [he,reconstructBatch_correct]

theorem contextBatch_pairs {n D T b d m : ℕ} (H : Memory.{u}) (e : Edge n)
    (ctx : H → Context (d := D) e T) (hc : Measurable ctx)
    (g : H → Generators n D b) (hg : Measurable g)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    (value (contextBatch (d := d) H e ctx hc g hg) s O).2=
      insertMany true (insertMany false s.2 (g s.1 (src e)) (batchResponse false (g s.1 (src e)) O))
        (g s.1 (dst e)) (batchResponse true (g s.1 (dst e)) O) := by
  simp only [contextBatch,value_map,bidirectional_value]

theorem contextBatch_no_failure {n D T b d m : ℕ} (H : Memory.{u}) (e : Edge n)
    (ctx : H → Context (d := D) e T) (hc : Measurable ctx)
    (g : H → Generators n D b) (hg : Measurable g)
    (s : State H D m) (O : OrthogonalHaar.Group D) :
    ¬failure (contextBatch (d := d) H e ctx hc g hg) s O := by
  simp only [contextBatch,failure_map]
  exact bidirectional_no_failure _ _ _ _ _ _ _

end Bilevel.TransportControllerMachine
