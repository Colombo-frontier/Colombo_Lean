import LowRank.GaussianQuerySpan

/-! Every original query direction lies in the final exposed space of its
measurable normalized simulation. Supplementary directions may enlarge this
space, so the conclusion is containment rather than equality. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def ambientQueriedSpan (d : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    AmbientOraclePolicy d n S → Matrix (Fin d) (Fin d) ℝ → S → Submodule ℝ (Fin d → ℝ)
  | 0, _, _, _, _, _ => ⊥
  | n + 1, _, _, policy, W, x =>
      (ℝ ∙ policy.1.1 x) ⊔ ambientQueriedSpan d n policy.2 W (x, W *ᵥ policy.1.1 x)

theorem reduceAmbientOracle_gaussian_span (d t r s n q : ℕ) {S T U : Type u}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (policy : AmbientOraclePolicy d n S) (mem : MeasurableStateMap T S)
    (vis : MeasurableStateMap T (VisibleFactorData d q (r + n)))
    (st : MeasurableStateMap U (FactorData d t q (r + n) (s + n))) (nm : MeasurableStateMap U T)
    (p : U × Matrix (Fin (r + n)) (Fin (s + n)) ℝ)
    (hvis : vis.1 (nm.1 p.1) = visibleFactorData (st.1 p.1)) (hst : (st.1 p.1).Orthogonal)
    (hreg : GaussianPolicy.Regular r s n (compileVisibleOracle d t r s n q
      (reduceAmbientOracle d r n q policy mem vis) st nm) p) :
    let gp := compileVisibleOracle d t r s n q (reduceAmbientOracle d r n q policy mem vis) st nm
    let X := representedMatrix (st.1 p.1) p.2
    exposedSpan (vis.1 (nm.1 p.1)) ⊔ ambientQueriedSpan d n policy (X * Xᵀ) (mem.1 (nm.1 p.1)) ≤
      exposedSpan (visibleFactorData (finalFactorData d t r s n q gp st.1
        (runGaussianPolicy r s n gp p).1)) := by
  induction n generalizing q S T U with
  | zero =>
    change exposedSpan (vis.1 (nm.1 p.1)) ⊔ ⊥ ≤ exposedSpan (visibleFactorData (st.1 p.1))
    rw [hvis, sup_bot_eq]
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + n + 1)) ℝ
    let uq := liftVisibleQuery (ambientPolicyDirection b policy.1 mem vis) st nm
    let st' := advanceFactorState b c uq st
    let nm' := advanceOracleMemory b c uq st nm
    let mem' := advanceReducedMemory b policy.1 mem vis
    let vis' := advanceReducedVisible b policy.1 mem vis
    let vp' := reduceAmbientOracle d r n (q + 1) policy.2 mem' vis'
    let gp' := compileVisibleOracle d t r s n (q + 1) vp' st' nm'
    let step := adaptiveGaussianStep b c uq.1 p
    change 0 < ‖(basisCoordinates c).symm step.1.2.1‖ ∧
      GaussianPolicy.Regular r s n gp' step at hreg
    have hstep := ambientStep_simulation b c policy.1 mem vis st nm p hvis hst (ne_of_gt hreg.1)
    have hmem : mem'.1 (nm'.1 step.1) =
        (mem.1 (nm.1 p.1), (representedMatrix (st.1 p.1) p.2 * (representedMatrix (st.1 p.1) p.2)ᵀ) *ᵥ
          policy.1.1 (mem.1 (nm.1 p.1))) := hstep.1
    have hmatch : vis'.1 (nm'.1 step.1) = visibleFactorData (st'.1 step.1) := hstep.2
    have horth : (st'.1 step.1).Orthogonal := updateFactorData_orthogonal b c _ _ _ hst
    have hrec : representedMatrix (st'.1 step.1) step.2 = representedMatrix (st.1 p.1) p.2 :=
      updateFactorData_preserves_matrix b c _ _ _
    have h := ih (q + 1) policy.2 mem' vis' st' nm' step hmatch horth hreg.2
    dsimp only at h
    rw [hrec, hmem] at h
    let K := exposedSpan (visibleFactorData (finalFactorData d t r s n (q + 1) gp' st'.1
      (runGaussianPolicy r s n gp' step).1))
    have hnewle : exposedSpan (vis'.1 (nm'.1 step.1)) ≤ K := le_sup_left.trans h
    have hold : exposedSpan (vis.1 (nm.1 p.1)) ≤ exposedSpan (vis'.1 (nm'.1 step.1)) := by
      change exposedSpan (vis.1 (nm.1 p.1)) ≤ exposedSpan (recoverVisibleFactorData b
        (reducedQueryDirection b (vis.1 (nm.1 p.1)) (policy.1.1 (mem.1 (nm.1 p.1)))) _ _)
      rw [exposedSpan_recover b _ (reducedQueryDirection_norm b _ _)]
      exact le_sup_left
    have hB : (vis.1 (nm.1 p.1)).2 * (vis.1 (nm.1 p.1)).2ᵀ = 1 := by
      rw [hvis]
      exact hst.2.1
    have hfirst : policy.1.1 (mem.1 (nm.1 p.1)) ∈ exposedSpan (vis'.1 (nm'.1 step.1)) :=
      original_query_mem_recovered_span b (vis.1 (nm.1 p.1)) hB _ _
    change exposedSpan (vis.1 (nm.1 p.1)) ⊔ ((ℝ ∙ policy.1.1 (mem.1 (nm.1 p.1))) ⊔
      ambientQueriedSpan d n policy.2
        (representedMatrix (st.1 p.1) p.2 * (representedMatrix (st.1 p.1) p.2)ᵀ)
        (mem.1 (nm.1 p.1),
          (representedMatrix (st.1 p.1) p.2 * (representedMatrix (st.1 p.1) p.2)ᵀ) *ᵥ
            policy.1.1 (mem.1 (nm.1 p.1)))) ≤ K
    exact sup_le (hold.trans hnewle)
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hnewle hfirst)) (le_sup_right.trans h))

theorem ambientOracle_original_span_ae (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      ambientQueriedSpan (r + n) n policy (p.2 * p.2ᵀ) p.1 ≤
        exposedSpan (visibleFactorData (ambientOracleFactors r s n policy p)) := by
  filter_upwards [gaussianPolicy_regular_ae r s n ν
    (compileGramOracle r s n (normalizedAmbientPolicy r s n policy)) hv] with p hreg
  have h := reduceAmbientOracle_gaussian_span (r + n) (s + n) r s n 0 policy
    (identityMemory S) (initialVisibleState (r + n) (s + n))
    (initialFactorState (r + n) (s + n)) (identityMemory S) p rfl
    (initialFactorData_orthogonal _ _) hreg
  simpa only [initialVisibleState, initialFactorState, identityMemory, id_eq,
    exposedSpan_initial, bot_sup_eq, initialFactorData_represents] using h

theorem ambientOracle_original_span_le_normalized_ae (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : AmbientOraclePolicy (r + n) n S)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      let K := visibleQueriedSpan (r + n) r n 0 (normalizedAmbientPolicy r s n policy) (p.2 * p.2ᵀ)
        (p.1, visibleFactorData (initialFactorData (r + n) (s + n)))
      ambientQueriedSpan (r + n) n policy (p.2 * p.2ᵀ) p.1 ≤ K ∧ Module.finrank ℝ K = n := by
  filter_upwards [ambientOracle_original_span_ae r s n ν policy hv,
    ambientOracle_querySpan_ae r s n ν policy hv] with p hp hq
  exact ⟨hq.1 ▸ hp, hq.2⟩

end
end LowRank
