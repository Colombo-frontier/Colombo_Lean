import Bilevel.MultiscaleOriginalExecution
import Bilevel.PartialLegendreJoint

/-! Full Euclidean gradient oracles for the literal macro-free scalar
family. The first lower component is exact, so its full variance is the
already proved second-component variance. -/
noncomputable section
open MeasureTheory
namespace Bilevel.MultiscaleMean
open CompensatedMean PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]
  [MeasurableSpace (Joint E (LowerSpace E))] [BorelSpace (Joint E (LowerSpace E))]
  {n : ℕ} (P : Parameters (E:=E) n)

def innerLowerFullOracle (σ : ℝ) (hscale : P.β*P.θ≤1) :
    FreshOracle.Oracle (Query:=InnerQuery E) (E:=Joint E (LowerSpace E))
      (BernoulliOracle.law (P.activationProbability σ) (P.activationProbability_le_one σ)) σ := by
  let O := P.freshOracle σ hscale
  let I : LowerSpace E →L[ℝ] Joint E (LowerSpace E) :=
    packLinear.comp ((0 : LowerSpace E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ (LowerSpace E)))
  have hI (y : LowerSpace E) : I y=pack (0:E) y := rfl
  have herror (q : InnerQuery E) (coin : Bool) :
      pack (P.sampleLowerX (P.activationProbability σ) q.1 q.2 coin)
        (P.sampleLowerY (P.activationProbability σ) q.1 q.2 coin)-
      pack (P.data.lowerX q.1 q.2) (P.data.lowerY q.1 q.2)=I (O.sample q coin-O.truth q) := by
    apply (WithLp.equiv 2 (E × LowerSpace E)).injective
    apply Prod.ext
    · change P.data.lowerX q.1 q.2-P.data.lowerX q.1 q.2=0
      exact sub_self _
    · rfl
  have hnorm (q : InnerQuery E) (coin : Bool) :
      ‖pack (P.sampleLowerX (P.activationProbability σ) q.1 q.2 coin)
        (P.sampleLowerY (P.activationProbability σ) q.1 q.2 coin)-
      pack (P.data.lowerX q.1 q.2) (P.data.lowerY q.1 q.2)‖=‖O.sample q coin-O.truth q‖ := by
    rw [herror,hI,PartialLegendre.norm_pack_zero_left]
  have hx : Measurable (fun q : InnerQuery E => P.data.lowerX q.1 q.2) :=
    ((uProj E).continuous.measurable.comp measurable_snd).const_smul (-P.L)
  have ht := packLinear.continuous.measurable.comp (hx.prodMk O.truth_measurable)
  have hs := packLinear.continuous.measurable.comp ((hx.comp measurable_fst).prodMk O.sample_measurable)
  refine {
    truth := fun q => pack (P.data.lowerX q.1 q.2) (P.data.lowerY q.1 q.2)
    sample := fun q coin => pack (P.sampleLowerX (P.activationProbability σ) q.1 q.2 coin)
      (P.sampleLowerY (P.activationProbability σ) q.1 q.2 coin)
    truth_measurable := ht
    sample_measurable := hs
    square_integrable := fun _ => Integrable.of_finite
    mean := ?_
    variance := ?_ }
  · intro q
    simp_rw [herror]
    have hi := I.integral_comp_comm (O.error_integrable q)
    simp only [FreshOracle.Oracle.error] at hi
    rw [hi,O.mean,map_zero]
  · intro q
    simpa only [hnorm] using O.variance q

def innerUpperFullOracle (σf σg : ℝ) :
    FreshOracle.Oracle (Query:=InnerQuery E) (E:=Joint E (LowerSpace E))
      (BernoulliOracle.law (P.activationProbability σg) (P.activationProbability_le_one σg)) σf := by
  have h := innerOriginalReply_measurable P (P.activationProbability σg)
  have hq : Measurable (fun q : InnerQuery E => (q,false)) := measurable_id.prodMk measurable_const
  have hu := packLinear.continuous.measurable.comp ((measurable_fst.comp h).comp hq)
  exact {
    truth := fun q => pack (P.data.upperX q.1 q.2) (P.data.upperY q.1 q.2)
    sample := fun q _ => pack (P.data.upperX q.1 q.2) (P.data.upperY q.1 q.2)
    truth_measurable := hu
    sample_measurable := hu.comp measurable_fst
    square_integrable := by intro q;simp
    mean := by intro q;simp
    variance := by intro q;simp only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),integral_zero];positivity }

end Bilevel.MultiscaleMean
