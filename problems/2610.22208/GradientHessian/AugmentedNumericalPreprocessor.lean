import GradientHessian.AugmentedNumericalDriver
import GradientHessian.DisclosurePreload
import GradientHessian.DisclosureCappedProgram
import GradientHessian.NumericalPriorCache

/-! Charged augmented preprocessing with a suspended policy initialization.
All prior readouts are obtained by the disclosure program before execution.
The external supply stop preserves the receipt that first supplies the mark. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalPreprocessor
open Classical HigherHierarchy HierarchyAddresses FrontierState TaskState
  NumericalCachedOracle AugmentedNumericalDriver

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (t : ℕ)
variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]

abbrev RuntimeState := RawNumericalExperiment.Auxiliary d n r J E H t Seed ×
  NumericalPreprocessor.Store d J × Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t

local notation "Run" => RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell)
  (E := E) (H := H) (Seed := Seed) (S := S) t

def initial (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) : Run :=
  (w,(fun _ => false,fun _ => 0),Sum.inl PUnit.unit)

variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (leaf : Leaf (t+1))
  (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
    (DirectionPolicyReplay.Point d J E H t)
    (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

def cache (j : Fin (4096*J^2+1)) (s : Run) : Cache d J :=
  (NumericalPreprocessor.forcing B j s.1.1,s.2.1.2)

def halt (j : Fin (4096*J^2+1)) (s : Run) : Bool :=
  AugmentedNumericalDriver.finished t s.2.2 ||
    AugmentedDisclosure.markStop leaf j (AugmentedNumericalDriver.state t s.2.2)

def mode (j : Fin (4096*J^2+1)) (s : Run) : Fin 4 :=
  if halt t leaf j s then 0 else
    if AugmentedNumericalDriver.product t leaf (fun _ => false) s.2.2 then 2 else 1

def stepReply (K : ℝ) (N : ℕ) (j : Fin (4096*J^2+1)) (s : Run) (Ay : Fin d → ℝ) : Run :=
  (s.1,s.2.1,AugmentedNumericalDriver.advance t P B fallback leaf policy K N (fun _ => false)
    s.1.2.2 s.1.2.1 (cache t B j s) ((NumericalOrdinaryProcedure.coordinates d).symm Ay) s.2.2)

def query (s : Run) : Fin d → ℝ :=
  NumericalOrdinaryProcedure.coordinates d
    (CensoredOracle.numericalMap t (AugmentedNumericalDriver.point t s.2.2))

def mark (j : Fin (4096*J^2+1)) (k : ℕ) (s : Run) : Fin d → ℝ :=
  if hk : k<4096*J^2+1 then NumericalOrdinaryProcedure.coordinates d
    (LowRank.matrixEuclideanMap B (NumericalPreprocessor.marks j s.1.1 ⟨k,hk⟩)) else 0

def write (k : ℕ) (q : Run × (Fin d → ℝ)) : Run :=
  if hk : k<4096*J^2+1 then
    (q.1.1,(Function.update q.1.2.1.1 ⟨k,hk⟩ true,
      Function.update q.1.2.1.2 ⟨k,hk⟩ ((NumericalOrdinaryProcedure.coordinates d).symm q.2)),q.1.2.2)
  else q.1

theorem initial_measurable : Measurable (initial (d := d) (n := n) (r := r) (J := J)
    (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  measurable_id.prodMk measurable_const

theorem cache_measurable (j : Fin (4096*J^2+1)) : Measurable (cache t B j : Run → Cache d J) :=
  ((NumericalPreprocessor.forcing_measurable B j).comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_snd.comp (measurable_fst.comp measurable_snd))

theorem halt_measurable (j : Fin (4096*J^2+1)) : Measurable (halt t leaf j : Run → Bool) :=
  (measurable_of_countable (fun q : Bool × Bool => q.1 || q.2)).comp
    (((AugmentedNumericalDriver.finished_measurable t).comp (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_of_countable (AugmentedDisclosure.markStop leaf j)).comp
        ((AugmentedNumericalDriver.state_measurable t).comp (measurable_snd.comp measurable_snd))))

theorem mode_measurable (j : Fin (4096*J^2+1)) : Measurable (mode t leaf j : Run → Fin 4) :=
  (measurable_of_countable (fun q : Bool × Bool => if q.1 then (0 : Fin 4) else if q.2 then 2 else 1)).comp
    ((halt_measurable t leaf j).prodMk
      ((AugmentedNumericalDriver.product_measurable t leaf (fun _ => false)).comp
        (measurable_snd.comp measurable_snd)))

theorem stepReply_measurable {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) :
    Measurable (fun q : Run × (Fin d → ℝ) => stepReply t P B fallback leaf policy K N j q.1 q.2) := by
  have hm : Measurable (fun q : Run × (Fin d → ℝ) =>
      ((((q.1.1.2.1,cache t B j q.1),q.1.1.2.2),(NumericalOrdinaryProcedure.coordinates d).symm q.2),q.1.2.2)) := by
    apply Measurable.prodMk
    · apply Measurable.prodMk
      · apply Measurable.prodMk
        · apply Measurable.prodMk
          · fun_prop
          · exact (cache_measurable t B j).comp measurable_fst
        · fun_prop
      · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
    · fun_prop
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((AugmentedNumericalDriver.advance_measurable t P B fallback leaf policy hK N (fun _ => false)).comp hm))

theorem query_measurable : Measurable (query (d := d) (n := n) (r := r) (J := J)
    (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  (NumericalOrdinaryProcedure.coordinates d).continuous.measurable.comp
    ((CensoredOracle.numericalMap (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
      (m := 4096*J^2) t).continuous.measurable.comp
      ((AugmentedNumericalDriver.point_measurable t).comp (measurable_snd.comp measurable_snd)))

theorem mark_measurable (j : Fin (4096*J^2+1)) (k : ℕ) : Measurable (mark t B j k : Run → Fin d → ℝ) := by
  unfold mark
  split_ifs with hk
  · exact (NumericalOrdinaryProcedure.coordinates d).continuous.measurable.comp
      ((LowRank.matrixEuclideanMap B).continuous.measurable.comp
        (((measurable_pi_apply ⟨k,hk⟩).comp (NumericalPreprocessor.marks_measurable j)).comp
          (measurable_fst.comp measurable_fst)))
  · exact measurable_const

theorem write_measurable (k : ℕ) : Measurable (write t k : Run × (Fin d → ℝ) → Run) := by
  unfold write
  split_ifs with hk
  · apply Measurable.prodMk
    · fun_prop
    · apply Measurable.prodMk
      · apply Measurable.prodMk
        · have hm : Measurable (fun q : Run × (Fin d → ℝ) => (q.1.2.1.1,true)) := by fun_prop
          exact (measurable_update' (a := (⟨k,hk⟩ : Fin (4096*J^2+1)))).comp hm
        · have hm : Measurable (fun q : Run × (Fin d → ℝ) =>
              (q.1.2.1.2,(NumericalOrdinaryProcedure.coordinates d).symm q.2)) := by
            apply Measurable.prodMk
            · fun_prop
            · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
          exact (measurable_update' (a := (⟨k,hk⟩ : Fin (4096*J^2+1)))).comp hm
      · fun_prop
  · exact measurable_fst

def baseProgram {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) : DisclosureCompiler.Program d Run where
  mode := mode t leaf j
  think := fun s => stepReply t P B fallback leaf policy K N j s 0
  query := query t
  mark := fun _ => 0
  next := fun q => stepReply t P B fallback leaf policy K N j q.1 q.2
  disclosed := Prod.fst
  mode_measurable := mode_measurable t leaf j
  think_measurable := (stepReply_measurable t P B fallback leaf policy hK N j).comp
    (measurable_id.prodMk measurable_const)
  query_measurable := query_measurable t
  mark_measurable := measurable_const
  next_measurable := stepReply_measurable t P B fallback leaf policy hK N j
  disclosed_measurable := measurable_fst

def program {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) :
    DisclosureCompiler.Program d (Run × ℕ) :=
  DisclosurePreload.program (baseProgram t P B fallback leaf policy hK N j)
    (mark t B j) (write t) (mark_measurable t B j) (write_measurable t)

def cappedProgram {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1)) :
    DisclosureCompiler.Program d ((Run × ℕ) × ℕ × ℕ) :=
  DisclosureCappedProgram.cap (program t P B fallback leaf policy hK N j)

theorem capped_calls {K : ℝ} (hK : 0<K) (N : ℕ) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (fuel q R : ℕ) (s : Run × ℕ) :
    (cappedProgram t P B fallback leaf policy hK N j).ordinaryCalls A readout fuel (s,q,R)≤q ∧
    (cappedProgram t P B fallback leaf policy hK N j).disclosures A readout fuel (s,q,R)≤R :=
  DisclosureCappedProgram.calls_le (program t P B fallback leaf policy hK N j) A readout fuel s q R

theorem initial_suspended (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed) :
    (initial (ell := ell) (S := S) t w).2.2=Sum.inl PUnit.unit := rfl

theorem initial_supply_halts (j : Fin (4096*J^2+1))
    (w : RawNumericalExperiment.Auxiliary d n r J E H t Seed)
    (hs : AugmentedDisclosure.markStop leaf j (TaskState.initial (ell := ell))=true) :
    mode t leaf j (initial (ell := ell) (S := S) t w)=0 := by
  simp only [mode,halt,initial,AugmentedNumericalDriver.finished,AugmentedNumericalDriver.state,hs,Bool.false_or,if_true]

end GradientHessian.AugmentedNumericalPreprocessor
