import NCConcave16991.PersistentProgramBasic
import NCConcave16991.OracleProgramControl
import Mathlib.Tactic.FunProp

/-! # The persistent inner solver as an actual reply-driven oracle program -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.PersistentProgram

abbrev OuterState (dx dy : ℕ) := PrimalSpace dx × JointSpace dx dy

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

abbrev InnerState (K : KnownDualDomain dy p.diameter) (dx : ℕ) :=
  (productDomain dx K) × PrimalSpace dx

def anchorPoint (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (s : OuterState dx dy) :
    productDomain dx K := ⟨jointPoint s.1 y0, hy0⟩

theorem anchorPoint_measurable (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    Measurable (anchorPoint (dx := dx) y0 hy0) :=
  ((WithLp.prod_continuous_toLp 2 (PrimalSpace dx) (DualSpace dy)).measurable.comp
    (measurable_fst.prodMk measurable_const)).subtype_mk

theorem correction_continuous (L μ : ℝ) (y0 : DualSpace dy) :
    Continuous (fun a : PrimalSpace dx × JointSpace dx dy => saddleCorrection L μ y0 a.1 a.2) := by
  apply (WithLp.prod_continuous_toLp 2 (PrimalSpace dx) (DualSpace dy)).comp
  exact (((continuous_const : Continuous (fun _ : PrimalSpace dx × JointSpace dx dy => (2 * L : ℝ))).smul
    (((WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.comp continuous_snd).sub continuous_fst)).prodMk
    ((continuous_const : Continuous (fun _ : PrimalSpace dx × JointSpace dx dy => μ)).smul
      (((WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.comp continuous_snd).sub continuous_const)))

abbrev InnerStepInput (k : ℕ) :=
  (InnerAlgorithm.Seed p.n (k + 1) × OuterState dx dy) × InnerState K dx

/-- The direct update only reads the two supplied signed-gradient replies. -/
def innerUpdate (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (k : ℕ)
    (a : InnerStepInput (p := p) (K := K) (dx := dx) k)
    (reply : JointSpace dx dy × JointSpace dx dy) : InnerState K dx :=
  (VariationalInequality.projection (productDomain dx K) (productDomain_nonempty dx K)
    (productDomain_closed dx K) (productDomain_convex dx K)
    ((a.2.1 : JointSpace dx dy) -
      InnerAlgorithm.sourceStepSize p.L (selectedDualRegularization p) •
        (a.1.2.2 + (reply.1 - reply.2) +
          saddleCorrection p.L (selectedDualRegularization p) y0 a.1.2.1 a.2.1)),
    ((k : ℝ) / (k + 1)) • a.2.2 +
      (1 / ((k : ℝ) + 1)) • (a.2.1 : JointSpace dx dy).fst)

theorem innerUpdate_measurable (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (k : ℕ) :
    Measurable (Function.uncurry (innerUpdate (p := p) (dx := dx) y0 hy0 k)) := by
  let A := InnerStepInput (p := p) (K := K) (dx := dx) k ×
    (JointSpace dx dy × JointSpace dx dy)
  have hzS : Measurable (fun a : A => a.1.2.1) := by fun_prop
  have hz : Measurable (fun a : A => (a.1.2.1 : JointSpace dx dy)) :=
    measurable_subtype_coe.comp hzS
  have hc : Measurable (fun a : A => a.1.1.2.1) := by fun_prop
  have he : Measurable (fun a : A => a.1.1.2.2) := by fun_prop
  have hr1 : Measurable (fun a : A => a.2.1) := by fun_prop
  have hr2 : Measurable (fun a : A => a.2.2) := by fun_prop
  have ho : Measurable (fun a : A => a.1.2.2) := by fun_prop
  have hreg := (correction_continuous p.L (selectedDualRegularization p) y0).measurable.comp (hc.prodMk hz)
  have hη : Measurable (fun _ : A => InnerAlgorithm.sourceStepSize p.L (selectedDualRegularization p)) :=
    measurable_const
  have hin := hz.sub (hη.smul ((he.add (hr1.sub hr2)).add hreg))
  have hp := (VariationalInequality.projection_lipschitz (productDomain dx K)
    (productDomain_nonempty dx K) (productDomain_closed dx K) (productDomain_convex dx K)).continuous.measurable.comp hin
  have hx := (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.measurable.comp hz
  have hα : Measurable (fun _ : A => ((k : ℝ) / (k + 1))) := measurable_const
  have hβ : Measurable (fun _ : A => (1 / ((k : ℝ) + 1))) := measurable_const
  exact hp.prodMk ((hα.smul ho).add (hβ.smul hx))

def innerStepProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (k : ℕ) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (InnerState K dx)
      (InnerStepInput (p := p) (K := K) (dx := dx) k) 2 :=
  OracleProgram.mapWithSeed
    (signedPair K (fun a => a.1.1.2) (by fun_prop)
      (fun a => a.2.1) (fun a => anchorPoint y0 hy0 a.1.2) (by fun_prop)
      ((anchorPoint_measurable y0 hy0).comp (by fun_prop)))
    (innerUpdate y0 hy0 k) (innerUpdate_measurable y0 hy0 k)

def innerProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) : (k : ℕ) →
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (InnerState K dx)
      (InnerAlgorithm.Seed p.n k × OuterState dx dy) (2 * k)
  | 0 => OracleProgram.pure (fun a => (anchorPoint y0 hy0 a.2, 0))
      (((anchorPoint_measurable y0 hy0).comp measurable_snd).prodMk measurable_const)
  | k + 1 => OracleProgram.castBudget
      (OracleProgram.bind
        (OracleProgram.withSeed (innerProgram y0 hy0 k)
          (fun a : InnerAlgorithm.Seed p.n (k + 1) × OuterState dx dy => (a.1.1, a.2))
          (by fun_prop))
        (innerStepProgram y0 hy0 k)) (by omega)

theorem eval_innerStepProgram (P : Problem p dx dy K) (y0 : DualSpace dy)
    (hy0 : y0 ∈ K.carrier) (k : ℕ) (a : InnerStepInput (p := p) (K := K) (dx := dx) k) :
    OracleProgram.eval (innerStepProgram y0 hy0 k) (oracleResponse P) a =
      innerUpdate y0 hy0 k a (signedComponentGradient P a.1.1.2 a.2.1,
        signedComponentGradient P a.1.1.2 (anchorPoint y0 hy0 a.1.2)) := by
  rw [innerStepProgram, OracleProgram.eval_mapWithSeed, eval_signedPair]

/-- The reply-driven program equals both direct stored-estimate trajectory and returned primal average. -/
theorem eval_innerProgram (P : Problem p dx dy K) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (k : ℕ) (ω : InnerAlgorithm.Seed p.n k) (s : OuterState dx dy) :
    OracleProgram.eval (innerProgram (p := p) (dx := dx) y0 hy0 k) (oracleResponse P) (ω, s) =
      (InnerAlgorithm.estimatedTrajectory (productDomain dx K) (productDomain_nonempty dx K)
        (productDomain_closed dx K) (productDomain_convex dx K) (signedComponentGradient P)
        (saddleCorrection p.L (selectedDualRegularization p) y0 s.1) (anchorPoint y0 hy0 s) s.2
        (InnerAlgorithm.sourceStepSize p.L (selectedDualRegularization p)) k ω,
      InnerAlgorithm.estimatedOutput (productDomain dx K) (productDomain_nonempty dx K)
        (productDomain_closed dx K) (productDomain_convex dx K) (fun z : JointSpace dx dy => z.fst)
        (signedComponentGradient P) (saddleCorrection p.L (selectedDualRegularization p) y0 s.1)
        (anchorPoint y0 hy0 s) s.2 (InnerAlgorithm.sourceStepSize p.L (selectedDualRegularization p)) k ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [innerProgram, OracleProgram.eval_castBudget, OracleProgram.eval_bind,
      OracleProgram.eval_withSeed, eval_innerStepProgram, ih]
    rfl

end NCConcave16991.PersistentProgram
