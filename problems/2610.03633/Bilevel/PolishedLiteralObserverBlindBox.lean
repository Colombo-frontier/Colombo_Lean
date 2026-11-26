import Bilevel.PolishedLiteralObserverCoupling
import Bilevel.RadialRegularity

/-! The actual two-frame observation event implies the literal blind
box at every virtual query. Radial compression handles arbitrary raw
query norms, with a strict factor-two margin. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry SourceFrameActions
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem compressed_inner_le {d : ℕ} (v x : Space d) (R c : ℝ)
    (hR : 0<R) (hc : 0≤c) (h : |⟪v,x⟫|≤c*‖x‖) :
    |⟪v,RadialWrapper.compress R x⟫|≤c*R := by
  rw [RadialWrapper.compress,real_inner_smul_right,abs_mul,
    abs_of_pos (RadialWrapper.scale_pos R x)]
  calc
    _≤RadialWrapper.scale R x*(c*‖x‖) :=
      mul_le_mul_of_nonneg_left h (RadialWrapper.scale_pos R x).le
    _=c*(RadialWrapper.scale R x*‖x‖) := by ring
    _≤c*R := mul_le_mul_of_nonneg_left (RadialWrapper.compressed_radius_bound R hR x) hc

theorem sqrt_radius (R τ : ℝ) (hR : 0<R) (hτ : 0<τ) :
    Real.sqrt (τ^2/(4*R^2))*R=τ/2 := by
  rw [Real.sqrt_div (sq_nonneg τ),Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
    Real.sqrt_sq hτ.le,Real.sqrt_sq hR.le]
  norm_num
  field_simp
  ring

variable {dx du : ℕ}
  [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St : Type} [MeasurableSpace St]
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (A : BorelAdaptive.Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
  (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V)
  (τ p : ℝ)

/-- The same virtual query satisfies all source blind-coordinate
inequalities on the two actual observer events. No query bound or
zero-respecting restriction is imposed on the algorithm. -/
theorem source_observed_blindBox (draws : ℕ → Bool) (s₀ : St) (N k : ℕ) (hk : k<N)
    (hRx : 0<P.macroNode.radius) (hRu : 0<P.radius) (hb : 0<P.macroNode.width) (hτ : 0<τ)
    (hxobs : SourceObserved (literalMacroRules P A τ p)
      ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2)) N 0
      (lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V draws (s₀,0) U,(⊥,∅)) U)
    (huobs : SourceObserved (literalMicroRules P A τ p) (τ^2/(4*P.radius^2)) N 0
      (lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U draws (s₀,0) V,(⊥,∅)) V) :
    let z := literalRun P A τ p draws U V k 0 (s₀,0)
    (framedParameters P U hU V hV).BlindBox
      ((macroSchedule (P.macroNode.n+1) (P.n+1)).count z.2)
      (sourceCounts (P.macroNode.n+1) (P.n+1) z.2) τ (A.query z.1) := by
  let Px := macroSchedule (P.macroNode.n+1) (P.n+1)
  let Pu := microSchedule ((P.macroNode.n+1)*(P.n+1))
  let z := literalRun P A τ p draws U V k 0 (s₀,0)
  let mx := lift Px V draws (s₀,0) U
  let mu := lift Pu U draws (s₀,0) V
  have hrunx := literal_macro_run P A τ p draws U V k 0 (s₀,0)
  have hrunu := literal_micro_run P A τ p draws U V k 0 (s₀,0)
  change (∀ j : Fin (P.macroNode.n+1),Px.count z.2 ≤ j.val →
    |(framedParameters P U hU V hV).macroNode.coordinates (A.query z.1).fst.fst j|<P.macroNode.width/4) ∧
    (∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),
      sourceCounts (P.macroNode.n+1) (P.n+1) z.2 i ≤ j.val →
      |(framedParameters P U hU V hV).coordinates i (A.query z.1).snd.fst j|<τ)
  constructor
  · intro j hj
    have hjrun : Px.count (run (literalMacroRules P A τ p) k 0 mx U).2.2.2.1 ≤ j.val := by
      rw [hrunx]
      exact hj
    have hraw := source_observed_query_inner Px (Nat.succ_pos _) A
      (macroEvaluator Pu (rawCounterReply P τ p))
      (macroEvaluator_measurable Pu (rawCounterReply P τ p) (rawCounterReply_measurable P τ p))
      sourceXQuery (fun _ => 0) sourceXQuery_measurable measurable_const sourceXOutput sourceXOutput_measurable
      _ (by positivity) N 0 k (mx,(⊥,∅)) U (initial_prefixKnown Px mx) hk hxobs j hjrun
    have hraw' : |⟪U j,(A.query z.1).fst.fst⟫|≤
        Real.sqrt ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2))*‖(A.query z.1).fst.fst‖ := by
      have hh := hraw.1
      change |⟪U j,(A.query (run (literalMacroRules P A τ p) k 0 mx U).2.2.1).fst.fst⟫|≤
        Real.sqrt ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2))*
          ‖(A.query (run (literalMacroRules P A τ p) k 0 mx U).2.2.1).fst.fst‖ at hh
      rw [hrunx] at hh
      exact hh
    have hc := compressed_inner_le (U j) (A.query z.1).fst.fst P.macroNode.radius _ hRx
      (Real.sqrt_nonneg _) hraw'
    rw [sqrt_radius _ _ hRx (by positivity)] at hc
    change |WrappedChain.coordinates P.macroNode.n P.macroNode.radius
      (PolishedTwoFrameBlocks.ofFrame P.macroNode.n U hU) (A.query z.1).fst.fst j|<P.macroNode.width/4
    rw [ChiPrefixEvaluation.coordinates_inner,PolishedTwoFrameBlocks.ofFrame_basis]
    exact hc.trans_lt (by linarith)
  · intro i j hj
    have hfut : Pu.count z.2 ≤ (finProdFinEquiv (i,j)).val := by
      by_contra hnot
      have hlt := (flatCounts_prefix_iff (a:=z.2) (Nat.succ_pos P.n) i j).mp (Nat.lt_of_not_ge hnot)
      change sourceCounts (P.macroNode.n+1) (P.n+1) z.2 i ≤ j.val at hj
      exact (Nat.not_lt_of_ge hj) hlt
    have hjrun : Pu.count (run (literalMicroRules P A τ p) k 0 mu V).2.2.2.1 ≤ (finProdFinEquiv (i,j)).val := by
      rw [hrunu]
      exact hfut
    have hraw := source_observed_query_inner Pu (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) A
      (microEvaluator Px (rawCounterReply P τ p))
      (microEvaluator_measurable Px (rawCounterReply P τ p) (rawCounterReply_measurable P τ p))
      sourceOuterUQuery sourceInnerUQuery sourceOuterUQuery_measurable sourceInnerUQuery_measurable
      sourceUOutput sourceUOutput_measurable _ (by positivity) N 0 k (mu,(⊥,∅)) V
      (initial_prefixKnown Pu mu) hk huobs (finProdFinEquiv (i,j)) hjrun
    have hraw' : |⟪V (finProdFinEquiv (i,j)),(A.query z.1).snd.fst⟫|≤
        Real.sqrt (τ^2/(4*P.radius^2))*‖(A.query z.1).snd.fst‖ := by
      have hh := hraw.2
      change |⟪V (finProdFinEquiv (i,j)),(A.query (run (literalMicroRules P A τ p) k 0 mu V).2.2.1).snd.fst⟫|≤
        Real.sqrt (τ^2/(4*P.radius^2))*
          ‖(A.query (run (literalMicroRules P A τ p) k 0 mu V).2.2.1).snd.fst‖ at hh
      rw [hrunu] at hh
      exact hh
    have hc := compressed_inner_le (V (finProdFinEquiv (i,j))) (A.query z.1).snd.fst P.radius _ hRu
      (Real.sqrt_nonneg _) hraw'
    rw [sqrt_radius _ _ hRu hτ] at hc
    change |WrappedChain.coordinates P.n P.radius (PolishedTwoFrameBlocks.microBlockFrame V hV i)
      (A.query z.1).snd.fst j|<τ
    rw [ChiPrefixEvaluation.coordinates_inner,PolishedTwoFrameBlocks.microBlockFrame_basis]
    exact hc.trans_lt (by linarith)

end Bilevel.PolishedLiteralActualObserver
