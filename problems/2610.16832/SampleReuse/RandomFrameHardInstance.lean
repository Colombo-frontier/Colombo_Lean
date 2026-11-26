import SampleReuse.RandomFrameLowerBound

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory SecondOrder RandomizedFO2003 Rotations
open scoped InnerProductSpace ENNReal

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Averaging chooses one fixed instance, while retaining the algorithm's own
random coins. No measurability assumption is needed on a smaller success event. -/
theorem exists_fiber_bound (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set (Ω × Ξ)) (hs : MeasurableSet s) {δ δ' : ℝ}
    (hprod : (μ.prod ν).real s ≤ δ) (hδ : δ < δ') :
    ∃ θ, μ.real ((fun ω => (ω, θ)) ⁻¹' s) ≤ δ' := by
  by_contra hn
  have hge (θ : Ξ) : ENNReal.ofReal δ' ≤ μ ((fun ω => (ω, θ)) ⁻¹' s) :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
      (le_of_lt (lt_of_not_ge (not_exists.mp hn θ)))
  have hp : ENNReal.ofReal δ' ≤ (μ.prod ν) s := by
    rw [Measure.prod_apply_symm hs]
    calc
      _ = ∫⁻ _θ : Ξ, ENNReal.ofReal δ' ∂ν := by simp
      _ ≤ _ := lintegral_mono hge
  have hl : δ' ≤ (μ.prod ν).real s :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hp
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem measurableSet_projectionBadEvent {m N : ℕ} (hN : N < m) (e : Fin m → E)
    (q : ∀ r : Fin (N+1), Ω × (Fin r.val → E) → E) (hq : ∀ r, Measurable (q r))
    (R t : ℝ) : MeasurableSet (projectionBadEvent hN e q R t) := by
  unfold projectionBadEvent
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro j
  by_cases hrj : r.val ≤ j.val
  · simp only [hrj, true_and]
    have hquery : Measurable (fun p : Ω × Rotation E =>
        q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k)))) :=
      (hq r).comp (measurable_fst.prodMk (measurable_pi_lambda _
        (fun k => (measurable_orbit E (e (prefixIndex hN r k))).comp measurable_snd)))
    have hinner : Measurable (fun p : Ω × Rotation E =>
        ⟪q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k))),
          isometry E p.2 (e j)⟫_ℝ) :=
      (show Continuous (fun z : E × E => ⟪z.1,z.2⟫_ℝ) from
        continuous_fst.inner continuous_snd).measurable.comp
          (hquery.prodMk ((measurable_orbit E (e j)).comp measurable_snd))
    exact (measurableSet_le hquery.norm measurable_const).inter
      (measurableSet_le (measurable_const (a := t)) hinner.abs)
  · simp only [hrj, false_and, Set.setOf_false, MeasurableSet.empty]

theorem curvature_radial_exists_hard_frame {d T N : ℕ} (hN : N < T+1)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      query n p.1 p.2))
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) {A β b ε γ R t δ δ' : ℝ}
    (hA : 0 ≤ A) (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 < R) (hγ : 0 < γ)
    (ht : 0 < t) (hβt : β*t ≤ 1/2) (hδ : 0 < δ) (hδ' : δ < δ')
    (hnegative : 8*γ ≤ A*β^2*Real.exp (-(9:ℝ)/4))
    (hwall : 2*b/R ≤ γ)
    (htransverse : 4*(A*β^2*curvatureCoreConstant)/(β*R) ≤ γ)
    (hexterior : ε < b-A*β*(curvatureCoreConstant*Real.sqrt (T+1:ℕ)))
    (hdim : 2*(2*R)^2*Real.log (2*((T+1)*(N+1):ℕ)/δ) ≤ ((d-N:ℕ):ℝ)*t^2)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (ho : Measurable (fun p : Ω × (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      output p.1 p.2)) :
    ∃ V : Rotation (Point d), μ.real {ω |
      IsSOSP (radialGlobalization (curvatureFrameCore (rotatedEmbedding U V) A β) b R) ε γ
        (radialFullOutput query (rotatedEmbedding U V) A β b R N output ω)} ≤ δ' := by
  let q := radialPolicyStages (T := T) query A β b R N output
  let s := projectionBadEvent hN (fun i => U (blockUnit i (1:ℝ))) q (2*R) t
  have hqm := measurable_radialPolicyStages (T := T) query hq A β b hR N output ho
  have hs : MeasurableSet s := measurableSet_projectionBadEvent hN _ q hqm (2*R) t
  have hprob : (μ.prod (haarLaw (Point d))).real s ≤ δ := by
    have hbnd := projectionBadEvent_bound hN μ (fun i => U (blockUnit i (1:ℝ)))
      (embedding_columns_orthonormal U) q hqm (by positivity : 0 < 2*R) ht
    have hconf := spherical_union_confidence ((T+1)*(N+1)) (d-N)
      (show 0 < 2*R by positivity) hδ hdim
    apply hbnd.trans
    simpa only [finrank_euclideanSpace, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hconf
  obtain ⟨V,hV⟩ := exists_fiber_bound μ (haarLaw (Point d)) s hs hprob hδ'
  refine ⟨V, (measureReal_mono (μ := μ) ?_).trans hV⟩
  intro ω hω
  exact radial_success_subset_bad hN query U A β b ε γ hR hβ.le hβt output
    (fun V x hsosp => curvature_radial_sosp_completed (rotatedEmbedding U V)
      hA hβ hb hR hγ hnegative hwall htransverse hexterior hsosp) hω

end SampleReuse.RandomFrame
