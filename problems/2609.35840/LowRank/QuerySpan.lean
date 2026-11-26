import LowRank.QueryBasisUpdate
import LowRank.AmbientQueryReduction
import LowRank.FactorInitial

/-! The leading columns span exactly the directions that have been queried,
in addition to any initially exposed space. Arbitrary-query reduction puts
the original direction into the next exposed space, including zero residual. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section
universe u

def exposedSpan {d q r : ℕ} (vis : VisibleFactorData d q r) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (Set.range (fun j : Fin q => fun i => vis.2 i (Sum.inl j)))

theorem exposedSpan_initial (d t : ℕ) :
    exposedSpan (visibleFactorData (initialFactorData d t)) = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨j, _⟩
  exact Fin.elim0 j

theorem exposedSpan_finrank {d q r : ℕ} (vis : VisibleFactorData d q r) :
    Module.finrank ℝ (exposedSpan vis) ≤ q := by
  simpa only [Fintype.card_fin] using
    (finrank_range_le_card (R := ℝ) (fun j : Fin q => fun i => vis.2 i (Sum.inl j)))

theorem exposedSpan_finrank_eq {d q r : ℕ} (vis : VisibleFactorData d q r)
    (hB : vis.2ᵀ * vis.2 = 1) : Module.finrank ℝ (exposedSpan vis) = q := by
  have hinj : Function.Injective vis.2.mulVec := by
    intro x y h
    have hx := congrArg (fun z => vis.2ᵀ *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using hx
  have hl := (Matrix.mulVec_injective_iff).mp hinj
  have hh := hl.comp Sum.inl (Sum.inl_injective)
  simpa only [Fintype.card_fin] using (finrank_span_eq_card hh)

theorem exposed_head_mem {d q r : ℕ} (vis : VisibleFactorData d q r) (x : Fin q → ℝ) :
    vis.2 *ᵥ Sum.elim x 0 ∈ exposedSpan vis := by
  have heq : vis.2 *ᵥ Sum.elim x 0 = (vis.2.submatrix id Sum.inl) *ᵥ x := by
    ext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  rw [heq]
  change _ ∈ Submodule.span ℝ (Set.range (vis.2.submatrix id Sum.inl).col)
  rw [← Matrix.range_mulVecLin]
  exact ⟨x, rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d q r : ℕ}

theorem exposedSpan_recover (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (hu : ‖(basisCoordinates b).symm u‖ = 1)
    (vis : VisibleFactorData d q (r + 1)) (reply : Fin d → ℝ) :
    exposedSpan (recoverVisibleFactorData b u vis reply) = exposedSpan vis ⊔ ℝ ∙ ambientQuery vis u := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · change (fun i => (recoverVisibleFactorData b u vis reply).2 i (Sum.inl 0)) ∈ _
      rw [recoverVisibleFactorData_query_column b u hu]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · change (fun i => (recoverVisibleFactorData b u vis reply).2 i (Sum.inl j.succ)) ∈ _
      rw [recoverVisibleFactorData_old_column b u]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change (fun i => vis.2 i (Sum.inl j)) ∈ _
      rw [← recoverVisibleFactorData_old_column b u vis reply j]
      exact Submodule.subset_span ⟨j.succ, rfl⟩
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      rw [← recoverVisibleFactorData_query_column b u hu vis reply]
      exact Submodule.subset_span ⟨0, rfl⟩

theorem original_query_mem_recovered_span (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (vis : VisibleFactorData d q (r + 1)) (hB : vis.2 * vis.2ᵀ = 1) (v reply : Fin d → ℝ) :
    v ∈ exposedSpan (recoverVisibleFactorData b (reducedQueryDirection b vis v) vis reply) := by
  rw [exposedSpan_recover b _ (reducedQueryDirection_norm b vis v)]
  have hmem : vis.2 *ᵥ Sum.elim (headQueryCoordinates vis v) 0 +
      ambientQuery vis (tailQueryCoordinates vis v) ∈
      exposedSpan vis ⊔ ℝ ∙ ambientQuery vis (reducedQueryDirection b vis v) := by
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left (exposed_head_mem vis _)
    · rw [← ambientQuery_scaled_direction b vis v]
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  simpa only [ambient_query_split vis hB v] using hmem

def visibleQueriedSpan (d r : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    VisibleOraclePolicy d r n q S → Matrix (Fin d) (Fin d) ℝ →
    S × VisibleFactorData d q (r + n) → Submodule ℝ (Fin d → ℝ)
  | 0, _, _, _, _, _, _ => ⊥
  | n + 1, q, _, _, policy, W, p =>
      (ℝ ∙ ambientQuery p.2 (policy.1.1 p)) ⊔ visibleQueriedSpan d r n (q + 1) policy.2 W
        (visibleOracleStep (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ) policy.1.1 W p)

theorem runVisibleOracle_exposedSpan (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) (hunit : VisibleOraclePolicy.IsUnit d r n q policy)
    (W : Matrix (Fin d) (Fin d) ℝ) (p : S × VisibleFactorData d q (r + n)) :
    exposedSpan (runVisibleOracle d r n q policy W p).2 =
      exposedSpan p.2 ⊔ visibleQueriedSpan d r n q policy W p := by
  induction n generalizing q S with
  | zero => exact (sup_bot_eq _).symm
  | succ n ih =>
    simp only [runVisibleOracle, visibleQueriedSpan]
    rw [ih (q + 1) policy.2 hunit.2]
    change exposedSpan (recoverVisibleFactorData _ (policy.1.1 p) p.2 _) ⊔ _ = _
    rw [exposedSpan_recover _ _ (hunit.1 p)]
    exact sup_assoc _ _ _

end
end LowRank
