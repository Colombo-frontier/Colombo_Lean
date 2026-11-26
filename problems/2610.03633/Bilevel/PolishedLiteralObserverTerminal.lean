import Bilevel.PolishedLiteralObserverBlindBox

/-! The terminal projection insertions control the actual outer output.
For the micro coordinates they control b_u(kappa*w), since the inserted
raw w and its public scalar multiple lie in the same observed span. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry SourceFrameActions
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {dx du : ℕ}
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))

/-- The source analytic prefix-barrier premise is geometric and applies
to every outer point with the specified unexposed-coordinate thresholds. -/
def PrefixSmall (κ : ℝ) (a : ℕ) (τx τu : ℝ) (y : Joint (Space dx) (Space du)) : Prop :=
  (∀ j : Fin (P.macroNode.n+1),(macroSchedule (P.macroNode.n+1) (P.n+1)).count a ≤ j.val →
    |P.macroNode.coordinates y.fst j|≤τx/2) ∧
  (∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),sourceCounts (P.macroNode.n+1) (P.n+1) a i ≤ j.val →
    |P.coordinates i (κ • y.snd) j|≤τu/2)

variable [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St : Type} [MeasurableSpace St]
  (A : BorelAdaptive.Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
  (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V)
  (τ p : ℝ)

theorem source_observed_terminal_prefix (draws : ℕ → Bool) (s₀ : St) (N : ℕ) (κ τx τu : ℝ)
    (hRx : 0<P.macroNode.radius) (hRu : 0<P.radius) (hτx : 0<τx) (hτu : 0<τu)
    (hxobs : SourceObserved (literalMacroRules P A τ p) (τx^2/(4*P.macroNode.radius^2)) N 0
      (lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V draws (s₀,0) U,(⊥,∅)) U)
    (huobs : SourceObserved (literalMicroRules P A τ p) (τu^2/(4*P.radius^2)) N 0
      (lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U draws (s₀,0) V,(⊥,∅)) V) :
    let z := literalRun P A τ p draws U V N 0 (s₀,0)
    PrefixSmall (framedParameters P U hU V hV) κ z.2 τx τu (A.output z.1) := by
  let Px := macroSchedule (P.macroNode.n+1) (P.n+1)
  let Pu := microSchedule ((P.macroNode.n+1)*(P.n+1))
  let z := literalRun P A τ p draws U V N 0 (s₀,0)
  let mx := lift Px V draws (s₀,0) U
  let mu := lift Pu U draws (s₀,0) V
  have hrunx := literal_macro_run P A τ p draws U V N 0 (s₀,0)
  have hrunu := literal_micro_run P A τ p draws U V N 0 (s₀,0)
  constructor
  · intro j hj
    have hjrun : Px.count (run (literalMacroRules P A τ p) N 0 mx U).2.2.2.1 ≤ j.val := by
      rw [hrunx]
      exact hj
    have hraw := source_observed_output_inner Px (Nat.succ_pos _) A
      (macroEvaluator Pu (rawCounterReply P τ p))
      (macroEvaluator_measurable Pu (rawCounterReply P τ p) (rawCounterReply_measurable P τ p))
      sourceXQuery (fun _ => 0) sourceXQuery_measurable measurable_const sourceXOutput sourceXOutput_measurable
      _ (by positivity) N 0 (mx,(⊥,∅)) U (initial_prefixKnown Px mx) hxobs j hjrun
    have hraw' : |⟪U j,(A.output z.1).fst⟫|≤Real.sqrt (τx^2/(4*P.macroNode.radius^2))*‖(A.output z.1).fst‖ := by
      change |⟪U j,(A.output (run (literalMacroRules P A τ p) N 0 mx U).2.2.1).fst⟫|≤
        Real.sqrt (τx^2/(4*P.macroNode.radius^2))*
          ‖(A.output (run (literalMacroRules P A τ p) N 0 mx U).2.2.1).fst‖ at hraw
      rw [hrunx] at hraw
      exact hraw
    have hc := compressed_inner_le (U j) (A.output z.1).fst P.macroNode.radius _ hRx (Real.sqrt_nonneg _) hraw'
    rw [sqrt_radius _ _ hRx hτx] at hc
    change |WrappedChain.coordinates P.macroNode.n P.macroNode.radius
      (PolishedTwoFrameBlocks.ofFrame P.macroNode.n U hU) (A.output z.1).fst j|≤τx/2
    rw [ChiPrefixEvaluation.coordinates_inner,PolishedTwoFrameBlocks.ofFrame_basis]
    exact hc
  · intro i j hj
    have hfut : Pu.count z.2 ≤ (finProdFinEquiv (i,j)).val := by
      by_contra hnot
      have hlt := (flatCounts_prefix_iff (a:=z.2) (Nat.succ_pos P.n) i j).mp (Nat.lt_of_not_ge hnot)
      exact (Nat.not_lt_of_ge hj) hlt
    have hjrun : Pu.count (run (literalMicroRules P A τ p) N 0 mu V).2.2.2.1 ≤ (finProdFinEquiv (i,j)).val := by
      rw [hrunu]
      exact hfut
    have hraw := source_observed_output_inner Pu (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) A
      (microEvaluator Px (rawCounterReply P τ p))
      (microEvaluator_measurable Px (rawCounterReply P τ p) (rawCounterReply_measurable P τ p))
      sourceOuterUQuery sourceInnerUQuery sourceOuterUQuery_measurable sourceInnerUQuery_measurable
      sourceUOutput sourceUOutput_measurable _ (by positivity) N 0 (mu,(⊥,∅)) V
      (initial_prefixKnown Pu mu) huobs (finProdFinEquiv (i,j)) hjrun
    have hraw' : |⟪V (finProdFinEquiv (i,j)),(A.output z.1).snd⟫|≤
        Real.sqrt (τu^2/(4*P.radius^2))*‖(A.output z.1).snd‖ := by
      change |⟪V (finProdFinEquiv (i,j)),(A.output (run (literalMicroRules P A τ p) N 0 mu V).2.2.1).snd⟫|≤
        Real.sqrt (τu^2/(4*P.radius^2))*
          ‖(A.output (run (literalMicroRules P A τ p) N 0 mu V).2.2.1).snd‖ at hraw
      rw [hrunu] at hraw
      exact hraw
    have hscaled : |⟪V (finProdFinEquiv (i,j)),κ • (A.output z.1).snd⟫|≤
        Real.sqrt (τu^2/(4*P.radius^2))*‖κ • (A.output z.1).snd‖ := by
      rw [real_inner_smul_right,abs_mul,norm_smul,Real.norm_eq_abs]
      calc
        _≤|κ| *(Real.sqrt (τu^2/(4*P.radius^2))*‖(A.output z.1).snd‖) :=
          mul_le_mul_of_nonneg_left hraw' (abs_nonneg _)
        _=Real.sqrt (τu^2/(4*P.radius^2))*(|κ| *‖(A.output z.1).snd‖) := by ring
    have hc := compressed_inner_le (V (finProdFinEquiv (i,j))) (κ • (A.output z.1).snd) P.radius _ hRu
      (Real.sqrt_nonneg _) hscaled
    rw [sqrt_radius _ _ hRu hτu] at hc
    change |WrappedChain.coordinates P.n P.radius (PolishedTwoFrameBlocks.microBlockFrame V hV i)
      (κ • (A.output z.1).snd) j|≤τu/2
    rw [ChiPrefixEvaluation.coordinates_inner,PolishedTwoFrameBlocks.microBlockFrame_basis]
    exact hc

end Bilevel.PolishedLiteralActualObserver
