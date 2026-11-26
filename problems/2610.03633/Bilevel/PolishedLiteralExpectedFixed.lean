import Bilevel.PolishedLiteralHaarBorel
import Bilevel.PolishedLiteralExpectedDimension
import Bilevel.PolishedLiteralExpectedBridge

/-! The fixed-horizon literal certificate on the SAME ordinary hard-prior
sample space used by actual stopping costs and fixed-instance extraction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry BorelAdaptive PolishedProjectionDimension
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem run_response_congr {S Q O Y I J C : Type*}
    [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
    [MeasurableSpace I] [MeasurableSpace J] [MeasurableSpace C]
    (A : Program S Q O Y) (r : I → Q → C → O) (s : J → Q → C → O)
    (i : I) (j : J) (h : ∀ q c,r i q c=s j q c) (draws : ℕ → C) (initial : S) :
    ∀ n,BorelAdaptive.run A r i draws initial n=BorelAdaptive.run A s j draws initial n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BorelAdaptive.run,BorelAdaptive.run,ih]
    unfold BorelAdaptive.step
    split <;> simp only [h]

variable {dx du : ℕ}
  [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St Private : Type} [MeasurableSpace St] [MeasurableSpace Private]
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (A : Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (hx : P.macroNode.n+1≤dx) (hu : (P.macroNode.n+1)*(P.n+1)≤du)

omit [BorelSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem haar_originalRun_first (τ p : ℝ) (g : HaarPoint (dx:=dx) (du:=du))
    (draws : ℕ → Bool) (s : St) (N : ℕ) :
    (originalRun P A (HaarFrame.frame _ _ hx g.1) (HaarFrame.frame_orthonormal _ _ hx g.1)
      (HaarFrame.frame _ _ hu g.2) (HaarFrame.frame_orthonormal _ _ hu g.2) τ p draws N 0 (s,0)).1=
      BorelAdaptive.run A (haarResponse P hx hu τ p) g draws s N := by
  rw [originalRun_first_eq_run]
  exact run_response_congr A _ _ () g (by intros;rfl) draws s N

/-- Fixed-horizon 13/16 probability on Frame × (Private × fresh stream),
with the actual original response and the actual capped output. -/
theorem seeded_fixed_probability (initial : Private → St) (hi : Measurable initial)
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (κ τ p ε : ℝ) (hp : 0<p) (hp1 : p≤1) (N : ℕ)
    (hN : (N:ℝ)≤(((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(16*p))
    (hRx : 0<P.macroNode.radius) (hRu : 0<P.radius)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hτb : τ≤P.macroNode.width) (hδsc : ∀ j,j<P.J → τ≤P.δ j)
    (hdx : sourceDimension (N+1) (P.macroNode.n+1) P.macroNode.radius (P.macroNode.width/4) (1/8)≤dx)
    (hdu : sourceDimension (2*N+1) ((P.macroNode.n+1)*(P.n+1)) P.radius τ (1/8)≤du)
    (hbarrier : ∀ (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
      (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V),
      PrefixBarrier (framedParameters P U hU V hV) κ (P.macroNode.width/4) τ ε) :
    13/16≤(((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)).prod
      (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | 8*ε≤haarLoss P hx hu κ (seededCapped A (haarResponse P hx hu τ p) initial N z)} := by
  obtain ⟨_,_,hbase⟩ := conditional_fixed_horizon P A initial hi ρ κ τ p ε hp hp1 N hN
    hRx hRu hb hβ hτ hτβ hτb hδsc hdx hdu hbarrier
  let ν := (OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)
  let seedLaw := ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))
  let G : Set (Sample (HaarPoint (dx:=dx) (du:=du)) Private Bool) :=
    {z | 8*ε≤haarLoss P hx hu κ (seededCapped A (haarResponse P hx hu τ p) initial N z)}
  have hr := haarResponse_measurable P hx hu τ p hb hβ hτ hτβ hτb hδsc
  have hG : MeasurableSet G := measurableSet_le measurable_const
    ((haarLoss_measurable P hx hu κ).comp (seededCapped_measurable A (haarResponse P hx hu τ p) hr initial hi N))
  have he := (Measure.measurePreserving_swap (μ:=seedLaw) (ν:=ν)).measure_preimage hG.nullMeasurableSet
  have hpre : 13/16≤(seedLaw.prod ν).real (Prod.swap ⁻¹' G) := by
    convert hbase using 1
    congr 1
    ext z
    change (8*ε≤haarLoss P hx hu κ (seededCapped A (haarResponse P hx hu τ p) initial N (z.2,z.1))) ↔
      (8*ε≤haarLoss P hx hu κ (z.2,A.output
        (originalRun P A (HaarFrame.frame _ _ hx z.2.1) (HaarFrame.frame_orthonormal _ _ hx z.2.1)
          (HaarFrame.frame _ _ hu z.2.2) (HaarFrame.frame_orthonormal _ _ hu z.2.2)
          τ p z.1.2 N 0 (initial z.1.1,0)).1))
    dsimp only [haarLoss,seededCapped,cappedOutput,seedInput]
    rw [haar_originalRun_first P A hx hu τ p z.2 z.1.2 (initial z.1.1) N]
  change 13/16≤(ν.prod seedLaw).real G
  rw [measureReal_def,←he]
  exact hpre

end Bilevel.PolishedLiteralActualObserver
