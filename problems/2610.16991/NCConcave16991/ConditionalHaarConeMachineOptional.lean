import NCConcave16991.ConditionalHaarConeMachineMeasurable
import NCConcave16991.ConditionalHaarOptionalAdaptiveUnion
import NCConcave16991.ConditionalHaarProduct

/-!
# Exact selected-block optional-Haar representation of the reference machine

Fixing all other row blocks turns the actual phased machine into the proved
optional column-reveal process. Non-selected requests receive their actual
fixed answers; they reveal no column of the selected Haar matrix.
-/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

abbrev FrameSpace (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable (k n M : ℕ) (R : ℝ) (hR : 0 < R)

def selectedRead (hn : 0 < n) (e : Fin n ↪ Fin k) (j : Fin (M + 1))
    (s : State (FrameSpace k) n M R hR) : Option (Fin k) :=
  (request (FrameSpace k) n M R hR hn s).elim (fun _ ↦ none)
    (fun ri ↦ if ri.1 = j then some (e ri.2) else none)

def blockAnswer (j : Fin (M + 1)) (otherRows : Fin (M + 1) → Fin n → FrameSpace k)
    (r : Request n M) (a : FrameSpace k) : FrameSpace k :=
  r.elim (fun _ ↦ 0) (fun ri ↦ if ri.1 = j then a else otherRows ri.1 ri.2)

def combineRows (e : Fin n ↪ Fin k) (j : Fin (M + 1))
    (otherRows : Fin (M + 1) → Fin n → FrameSpace k) (Q : OrthogonalGroup k)
    (l : Fin (M + 1)) (i : Fin n) : FrameSpace k :=
  if l = j then orthogonalLinearIsometryEquiv Q (basisVector (e i)) else otherRows l i

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain (FrameSpace k) M R hR) (n := n)
    (dx := ConeProblem.primalDimension (FrameSpace k) M) Ω)

def selectedUpdate (seed : Ω) (hn : 0 < n) (q : ℝ) (j : Fin (M + 1))
    (otherRows : Fin (M + 1) → Fin n → FrameSpace k)
    (s : State (FrameSpace k) n M R hR) (a : FrameSpace k) : State (FrameSpace k) n M R hR :=
  update (FrameSpace k) n M R hR P seed hn q s
    (blockAnswer k n M j otherRows (request (FrameSpace k) n M R hR hn s) a)

theorem selected_step_eq (seed : Ω) (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (j : Fin (M + 1)) (otherRows : Fin (M + 1) → Fin n → FrameSpace k)
    (Q : OrthogonalGroup k) (s : State (FrameSpace k) n M R hR) :
    selectedUpdate k n M R hR P seed hn q j otherRows s
      ((selectedRead k n M R hR hn e j s).elim 0 (ColumnReveal.columnOracle Q)) =
    stepWithRows (FrameSpace k) n M R hR P seed hn q (combineRows k n M e j otherRows Q) s := by
  unfold selectedUpdate stepWithRows
  congr 1
  cases hr : request (FrameSpace k) n M R hR hn s with
  | inl _ => simp [blockAnswer, selectedRead, requestedAnswer, hr]
  | inr ri =>
    by_cases hj : ri.1 = j <;>
      simp [blockAnswer, selectedRead, requestedAnswer, combineRows, hr, hj, ColumnReveal.columnOracle]

theorem selected_run_eq (seed : Ω) (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (j : Fin (M + 1)) (otherRows : Fin (M + 1) → Fin n → FrameSpace k)
    (Q : OrthogonalGroup k) (t : ℕ) :
    OptionalReveal.run (selectedRead k n M R hR hn e j)
      (selectedUpdate k n M R hR P seed hn q j otherRows)
      (initial (FrameSpace k) n M R hR) (ColumnReveal.columnOracle Q) t =
    runWithRows (FrameSpace k) n M R hR P seed hn q (combineRows k n M e j otherRows Q) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [OptionalReveal.run, ih]
    rw [selected_step_eq]
    rfl

theorem selectedRead_measurable (hn : 0 < n) (e : Fin n ↪ Fin k) (j : Fin (M + 1)) :
    Measurable (selectedRead k n M R hR hn e j) := by
  let f : Request n M → Option (Fin k) := fun r ↦
    r.elim (fun _ ↦ none) (fun ri : RowIndex n M ↦ if ri.1 = j then some (e ri.2) else none)
  have hf : Measurable f := measurable_of_countable _
  exact hf.comp (request_measurable (FrameSpace k) n M R hR hn)

theorem blockAnswer_measurable (j : Fin (M + 1))
    (otherRows : Fin (M + 1) → Fin n → FrameSpace k) :
    Measurable (fun p : Request n M × FrameSpace k ↦ blockAnswer k n M j otherRows p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro r
  cases r with
  | inl _ => exact measurable_const
  | inr ri =>
    by_cases hj : ri.1 = j
    · simp only [blockAnswer, Sum.elim_inr, if_pos hj]
      exact measurable_id
    · simp only [blockAnswer, Sum.elim_inr, if_neg hj]
      exact measurable_const

theorem selectedUpdate_measurable (seed : Ω) (hn : 0 < n) (q : ℝ) (j : Fin (M + 1))
    (otherRows : Fin (M + 1) → Fin n → FrameSpace k) :
    Measurable (Function.uncurry (selectedUpdate k n M R hR P seed hn q j otherRows)) :=
  (update_measurable (FrameSpace k) n M R hR P hn q).comp
    ((measurable_const.prodMk measurable_fst).prodMk
      ((blockAnswer_measurable k n M j otherRows).comp
        (((request_measurable (FrameSpace k) n M R hR hn).comp measurable_fst).prodMk measurable_snd)))

def frameRows (e : Fin n ↪ Fin k) (Q : Fin (M + 1) → OrthogonalGroup k)
    (j : Fin (M + 1)) (i : Fin n) : FrameSpace k :=
  orthogonalLinearIsometryEquiv (Q j) (basisVector (e i))

theorem frameRows_measurable (e : Fin n ↪ Fin k) : Measurable (frameRows k n M e) :=
  measurable_pi_iff.mpr (fun j ↦ measurable_pi_iff.mpr (fun i ↦
    (continuous_orthogonalLinearIsometryEquiv_apply (basisVector (e i))).measurable.comp (measurable_pi_apply j)))

theorem frameRows_orthonormal (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (j : Fin (M + 1)) :
    Orthonormal ℝ (fun i ↦ frameRows k n M e Q j i) := rotated_rows_orthonormal e (Q j)

theorem combineRows_frame_insert (e : Fin n ↪ Fin k) (j : Fin (M + 1))
    (others : Fin M → OrthogonalGroup k) (Q : OrthogonalGroup k) :
    combineRows k n M e j (frameRows k n M e (Fin.insertNth j 1 others)) Q =
      frameRows k n M e (Fin.insertNth j Q others) := by
  apply funext
  refine (Fin.forall_iff_succAbove j).mpr ?_
  constructor
  · funext i
    simp [combineRows, frameRows]
  · intro l
    funext i
    simp [combineRows, frameRows, Fin.succAbove_ne]

end

end NCConcave16991.Haar.ConeMachine
