import NCBall.CountablePool
import NCBall.ShadowState
import NCBall.OracleTranscript

/-! # Measurable scalar strategies with arbitrary natural-number sample labels

The policy sees only its seed and past scalar values. Selecting a label for the
first time draws an independent sample; selecting it again reuses that sample.
-/

noncomputable section
open MeasureTheory Set
namespace NCBall

structure CountableRoomPolicy (S : Type*) [MeasurableSpace S] (n : ℕ) where
  point : (t : ℕ) → LinearHistory S t → Space n
  handle : (t : ℕ) → LinearHistory S t → ℕ
  measurable_point : ∀ t, Measurable (point t)
  measurable_handle : ∀ t, Measurable (handle t)

variable {S U Z I : Type*} [MeasurableSpace S] {n : ℕ}

def indexedSampleReply (point : (t : ℕ) → LinearHistory S t → Space n)
    (handle : (t : ℕ) → LinearHistory S t → I) (F : U → Z → Space n → ℝ)
    (t : ℕ) (h : LinearHistory S t) (w : U × (I → Z)) : ℝ :=
  F w.1 (w.2 (handle t h)) (point t h)

def sampleTranscript (point : (t : ℕ) → LinearHistory S t → Space n)
    (handle : (t : ℕ) → LinearHistory S t → I) (F : U → Z → Space n → ℝ)
    (t : ℕ) (w : U × (S × (I → Z))) : LinearHistory S t :=
  oracleTranscript (indexedSampleReply point handle F) t (w.2.1, (w.1, w.2.2))

omit [MeasurableSpace S] in
theorem sampleTranscript_succ (point : (t : ℕ) → LinearHistory S t → Space n)
    (handle : (t : ℕ) → LinearHistory S t → I) (F : U → Z → Space n → ℝ)
    (t : ℕ) (w : U × (S × (I → Z))) :
    sampleTranscript point handle F (t + 1) w =
      (sampleTranscript point handle F t w,
        F w.1 (w.2.2 (handle t (sampleTranscript point handle F t w)))
          (point t (sampleTranscript point handle F t w))) := rfl

theorem indexedSampleReply_measurable [MeasurableSpace U] [MeasurableSpace Z]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (point : (t : ℕ) → LinearHistory S t → Space n)
    (handle : (t : ℕ) → LinearHistory S t → I) (F : U → Z → Space n → ℝ)
    (hp : ∀ t, Measurable (point t)) (hh : ∀ t, Measurable (handle t))
    (hF : Measurable (fun w : U × (Z × Space n) => F w.1 w.2.1 w.2.2)) (t : ℕ) :
    Measurable (fun hw : LinearHistory S t × (U × (I → Z)) =>
      indexedSampleReply point handle F t hw.1 hw.2) := by
  have he : Measurable (fun zi : (I → Z) × I => zi.1 zi.2) :=
    measurable_from_prod_countable (fun i => measurable_pi_apply i)
  exact hF.comp ((measurable_fst.comp measurable_snd).prodMk
    ((he.comp ((measurable_snd.comp measurable_snd).prodMk
      ((hh t).comp measurable_fst))).prodMk ((hp t).comp measurable_fst)))

theorem sampleTranscript_measurable [MeasurableSpace U] [MeasurableSpace Z]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (point : (t : ℕ) → LinearHistory S t → Space n)
    (handle : (t : ℕ) → LinearHistory S t → I) (F : U → Z → Space n → ℝ)
    (hp : ∀ t, Measurable (point t)) (hh : ∀ t, Measurable (handle t))
    (hF : Measurable (fun w : U × (Z × Space n) => F w.1 w.2.1 w.2.2)) (t : ℕ) :
    Measurable (sampleTranscript point handle F t) :=
  (oracleTranscript_measurable _ (indexedSampleReply_measurable point handle F hp hh hF) t).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

def clampHandle (K j : ℕ) : Fin (K + 1) := if hj : j < K + 1 then ⟨j, hj⟩ else 0

theorem clampHandle_val {K j : ℕ} (hj : j < K + 1) : (clampHandle K j).val = j := by
  simp only [clampHandle, dif_pos hj]

def prefixPolicy (p : CountableRoomPolicy S n) (K : ℕ) : RoomQueryPolicy S n (K + 1) where
  point := p.point
  handle t h := clampHandle K (p.handle t h)
  measurable_point := p.measurable_point
  measurable_handle t := (measurable_of_countable (clampHandle K)).comp (p.measurable_handle t)

def prefixExperiment (K : ℕ) (w : U × (S × (ℕ → Z))) : U × (S × (Fin K → Z)) :=
  (w.1, (w.2.1, poolPrefix K w.2.2))

theorem prefixExperiment_law [MeasurableSpace U] [MeasurableSpace Z]
    (μ : Measure U) (ν : Measure S) (τ : Measure Z) [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure τ] (K : ℕ) :
    MeasurePreserving (prefixExperiment (U := U) (S := S) K)
      (μ.prod (ν.prod (Measure.infinitePi (fun _ : ℕ => τ))))
      (μ.prod (ν.prod (Measure.pi (fun _ : Fin K => τ)))) :=
  (MeasurePreserving.id μ).prod ((MeasurePreserving.id ν).prod (poolPrefix_law τ K))

theorem prefix_transcript_eq (p : CountableRoomPolicy S n) (F : U → Z → Space n → ℝ)
    (K N : ℕ) (w : U × (S × (ℕ → Z)))
    (hsafe : ∀ t < N, p.handle t (sampleTranscript p.point p.handle F t w) < K + 1) :
    sampleTranscript (prefixPolicy p K).point (prefixPolicy p K).handle F N
      (prefixExperiment (K + 1) w) = sampleTranscript p.point p.handle F N w := by
  suffices ∀ t ≤ N, sampleTranscript (prefixPolicy p K).point (prefixPolicy p K).handle F t
      (prefixExperiment (K + 1) w) = sampleTranscript p.point p.handle F t w from this N le_rfl
  intro t
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro ht
    rw [sampleTranscript_succ, sampleTranscript_succ, ih (by omega)]
    dsimp only [prefixPolicy, prefixExperiment, poolPrefix]
    rw [clampHandle_val (hsafe t (by omega))]

end NCBall
