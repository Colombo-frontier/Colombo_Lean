import GradientHessian.NumericalPreprocessingProgram
import GradientHessian.NumericalPriorCache
import GradientHessian.DisclosurePreload

noncomputable section
namespace GradientHessian.NumericalPreloadRuntime
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy FrontierState TaskState
  ComparisonController ComparisonControllerReplay ControllerMeasurable ControllerPolicyDriver
  GeometricRepair NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

open NumericalPreprocessor

def mark (j : Fin (4096*J^2+1)) (k : ℕ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) : Fin d → ℝ :=
  if hk : k<4096*J^2+1 then
    NumericalOrdinaryProcedure.coordinates d (LowRank.matrixEuclideanMap B (marks j s.1.1 ⟨k,hk⟩)) else 0

def write (k : ℕ)
    (q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ)) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  if hk : k<4096*J^2+1 then
    (q.1.1,(Function.update q.1.2.1.1 ⟨k,hk⟩ true,
      Function.update q.1.2.1.2 ⟨k,hk⟩ ((NumericalOrdinaryProcedure.coordinates d).symm q.2)),q.1.2.2) else q.1

theorem mark_measurable (j : Fin (4096*J^2+1)) (k : ℕ) :
    Measurable (mark (n := n) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) B t j k) := by
  by_cases hk : k<4096*J^2+1
  · unfold mark
    simp only [dif_pos hk]
    exact (NumericalOrdinaryProcedure.coordinates d).continuous.measurable.comp
      ((LowRank.matrixEuclideanMap B).continuous.measurable.comp
        (((measurable_pi_apply ⟨k,hk⟩).comp (marks_measurable j)).comp
          (measurable_fst.comp measurable_fst)))
  · unfold mark
    simp only [dif_neg hk]
    exact measurable_const

theorem write_measurable (k : ℕ) :
    Measurable (write (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t k) := by
  by_cases hk : k<4096*J^2+1
  · unfold write
    simp only [dif_pos hk]
    apply Measurable.prodMk
    · fun_prop
    · apply Measurable.prodMk
      · apply Measurable.prodMk
        · have hm : Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J)
              (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) => (q.1.2.1.1,true)) := by fun_prop
          have hh := (measurable_update' (a := (⟨k,hk⟩ : Fin (4096*J^2+1)))).comp hm
          simpa only [Function.comp_def] using hh
        · have hm : Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J)
              (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
              (q.1.2.1.2,(NumericalOrdinaryProcedure.coordinates d).symm q.2)) := by
            apply Measurable.prodMk
            · fun_prop
            · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
          have hh := (measurable_update' (a := (⟨k,hk⟩ : Fin (4096*J^2+1)))).comp hm
          simpa only [Function.comp_def] using hh
      · fun_prop
  · unfold write
    simp only [dif_neg hk]
    exact measurable_fst

/-- The supply boundary is checked by mode, after the phase transition.
The phase transition itself preserves the delivered before/after snapshots. -/
def unfrozenReply (K : ℝ) (j : Fin (4096*J^2+1))
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t)
    (Ay : Fin d → ℝ) : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (s.1,s.2.1,NumericalRuntime.advance P B fallback t leaf policy K (fun _ => false)
    s.1.2.1 (cache B t j s) ((NumericalOrdinaryProcedure.coordinates d).symm Ay) s.2.2)

theorem unfrozenReply_measurable {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
      unfrozenReply P B fallback t leaf policy K j q.1 q.2) := by
  have hm : Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
      (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
      (((q.1.1.2.1,cache B t j q.1),(NumericalOrdinaryProcedure.coordinates d).symm q.2),q.1.2.2)) := by
    apply Measurable.prodMk
    · apply Measurable.prodMk
      · apply Measurable.prodMk
        · fun_prop
        · exact (cache_measurable (n := n) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) B t j).comp measurable_fst
      · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
    · fun_prop
  have hr := (NumericalRuntime.advance_measurable (n := n) P B fallback t leaf policy hK (fun _ => false)).comp hm
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk hr)

def baseProgram {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    DisclosureCompiler.Program d (RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  { NumericalPreprocessor.program P B fallback t leaf policy hK j with
    mode := fun s => if halt t leaf j s then 0 else
      if NumericalDriverInstructions.product leaf (fun _ => false) s.2.2 then 2 else 1
    think := fun s => unfrozenReply P B fallback t leaf policy K j s 0
    next := fun q => unfrozenReply P B fallback t leaf policy K j q.1 q.2
    mode_measurable := (measurable_of_countable (fun z : Bool × Bool =>
      if z.1 then (0 : Fin 4) else if z.2 then 2 else 1)).comp
      ((halt_measurable t leaf j).prodMk
        ((NumericalDriverInstructions.product_measurable leaf (fun _ => false)).comp
          (measurable_snd.comp measurable_snd)))
    think_measurable := (unfrozenReply_measurable P B fallback t leaf policy hK j).comp
      (measurable_id.prodMk measurable_const)
    next_measurable := unfrozenReply_measurable P B fallback t leaf policy hK j }

def program {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    DisclosureCompiler.Program d ((RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) × ℕ) :=
  DisclosurePreload.program (baseProgram P B fallback t leaf policy hK j)
    (mark B t j) (write t) (mark_measurable B t j) (write_measurable t)

def filled (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ) (k : ℕ)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :
    RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
  (s.1,(fun q => if q.val<k then true else s.2.1.1 q,
    fun q => if q.val<k then NumericalPriorCache.value B j readout s.1.1 q else s.2.1.2 q),s.2.2)

theorem fill_update {M : ℕ} {V : Type*} (f g : Fin M → V) (k : ℕ) (hk : k<M) :
    (fun q => if q.val<k then f q else Function.update g ⟨k,hk⟩ (f ⟨k,hk⟩) q)=
      (fun q => if q.val<k+1 then f q else g q) := by
  funext q
  by_cases hq : q.val<k
  · simp only [if_pos hq,if_pos (show q.val<k+1 by omega)]
  · by_cases he : q=⟨k,hk⟩
    · subst q
      simp
    · have hh : ¬q.val<k+1 := by
        have hn : q.val≠k := fun hv => he (Fin.ext hv)
        omega
      simp only [if_neg hq,if_neg hh,Function.update_of_ne he]

theorem filled_write (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (k : ℕ) (hk : k<4096*J^2+1)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :
    filled B t j readout k (write t k (s,readout (mark B t j k s)))=filled B t j readout (k+1) s := by
  simp only [filled,write,mark,dif_pos hk,NumericalPriorCache.value]
  congr 1
  apply Prod.ext
  · apply Prod.ext
    · exact fill_update (fun _ => true) s.2.1.1 k hk
    · exact fill_update (fun q => (NumericalOrdinaryProcedure.coordinates d).symm
        (readout (NumericalOrdinaryProcedure.coordinates d (LowRank.matrixEuclideanMap B (marks j s.1.1 q))))) s.2.1.2 k hk
  · rfl

theorem prepared_exact (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (k : ℕ) (hk : k≤4096*J^2+1)
    (s : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :
    DisclosurePreload.prepared (mark B t j) (write t) readout k s=filled B t j readout k s := by
  induction k generalizing s with
  | zero => simp [DisclosurePreload.prepared,filled]
  | succ k ih =>
      rw [DisclosurePreload.prepared,ih (by omega)]
      exact filled_write B t j readout k (by omega) s

theorem prepared_initial (j : Fin (4096*J^2+1)) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (N : ℕ) (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) :
    DisclosurePreload.prepared (mark B t j) (write t) readout j.val (NumericalPreprocessor.initial (ell := ell) t policy N w)=
      (w,NumericalPriorCache.store B j readout w.1,ControllerPolicyDriver.initial policy N w.2.2 (TaskState.initial (ell := ell))) := by
  rw [prepared_exact B t j readout j.val (Nat.le_of_lt j.isLt)]
  simp only [filled,NumericalPreprocessor.initial,NumericalPriorCache.store]
  congr 1

end GradientHessian.NumericalPreloadRuntime
