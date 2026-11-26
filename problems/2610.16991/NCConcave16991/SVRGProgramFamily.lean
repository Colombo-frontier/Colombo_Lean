import NCConcave16991.PersistentProgramBasic
import NCConcave16991.OracleProgramControl
import NCConcave16991.SVRGConvergence
import Mathlib.Tactic.FunProp

/-!
# Reply-driven SVRG with a measurable public family of feasible domains

The parameter can contain a primal center and an extrapolated dual vector
computed from previous oracle replies. Feasible states carry that parameter,
so every query is feasible even for arbitrary supplied replies. The projection
is the actual Hilbert projection; its joint measurability is public geometry.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.SVRGProgram

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)
  (Θ : Type*) [MeasurableSpace Θ]

structure DomainFamily where
  carrier : Θ → Set (JointSpace dx dy)
  nonempty : ∀ θ, (carrier θ).Nonempty
  closed : ∀ θ, IsClosed (carrier θ)
  convex : ∀ θ, Convex ℝ (carrier θ)
  feasible : ∀ θ, carrier θ ⊆ productDomain dx K
  projection_measurable : Measurable (fun a : Θ × JointSpace dx dy ↦
    (VariationalInequality.projection (carrier a.1) (nonempty a.1) (closed a.1)
      (convex a.1) a.2 : JointSpace dx dy))

variable {K Θ}

abbrev Point (F : DomainFamily (dx := dx) K Θ) :=
  {a : Θ × JointSpace dx dy // a.2 ∈ F.carrier a.1}

/-- Parameter, anchor, cached full average, and current iterate. -/
abbrev Cache (F : DomainFamily (dx := dx) K Θ) :=
  {a : Θ × JointSpace dx dy × JointSpace dx dy × JointSpace dx dy //
    a.2.1 ∈ F.carrier a.1 ∧ a.2.2.2 ∈ F.carrier a.1}

abbrev parameter {F : DomainFamily (dx := dx) K Θ} (s : Cache F) : Θ := s.1.1
abbrev anchor {F : DomainFamily (dx := dx) K Θ} (s : Cache F) : JointSpace dx dy := s.1.2.1
abbrev estimate {F : DomainFamily (dx := dx) K Θ} (s : Cache F) : JointSpace dx dy := s.1.2.2.1
abbrev current {F : DomainFamily (dx := dx) K Θ} (s : Cache F) : JointSpace dx dy := s.1.2.2.2

def currentPoint {F : DomainFamily (dx := dx) K Θ} (s : Cache F) : Point F :=
  ⟨(parameter s, current s), s.2.2⟩

def originalPoint {F : DomainFamily (dx := dx) K Θ} (s : Point F) : productDomain dx K :=
  ⟨s.1.2, F.feasible s.1.1 s.2⟩

theorem currentPoint_measurable {F : DomainFamily (dx := dx) K Θ} :
    Measurable (currentPoint (F := F)) := by
  apply Measurable.subtype_mk
  exact (measurable_fst.comp measurable_subtype_coe).prodMk
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe)))

theorem originalPoint_measurable {F : DomainFamily (dx := dx) K Θ} :
    Measurable (originalPoint (F := F)) :=
  (measurable_snd.comp measurable_subtype_coe).subtype_mk

def cacheCurrent {F : DomainFamily (dx := dx) K Θ} (s : Cache F) : productDomain dx K :=
  originalPoint (currentPoint s)

def cacheAnchor {F : DomainFamily (dx := dx) K Θ} (s : Cache F) : productDomain dx K :=
  ⟨anchor s, F.feasible (parameter s) s.2.1⟩

theorem cacheCurrent_measurable {F : DomainFamily (dx := dx) K Θ} :
    Measurable (cacheCurrent (F := F)) :=
  originalPoint_measurable.comp currentPoint_measurable

theorem cacheAnchor_measurable {F : DomainFamily (dx := dx) K Θ} :
    Measurable (cacheAnchor (F := F)) :=
  (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)).subtype_mk

/-- The update uses only two returned signed component gradients and known data. -/
def cacheUpdate (F : DomainFamily (dx := dx) K Θ) (R : Θ × JointSpace dx dy → JointSpace dx dy)
    (η : ℝ) (s : Cache F) (reply : JointSpace dx dy × JointSpace dx dy) : Cache F :=
  let z := VariationalInequality.projection (F.carrier (parameter s))
    (F.nonempty _) (F.closed _) (F.convex _)
    (current s - η • (estimate s + (reply.1 - reply.2) + R (parameter s, current s)))
  ⟨(parameter s, anchor s, estimate s, (z : JointSpace dx dy)), ⟨s.2.1, z.2⟩⟩

theorem cacheUpdate_measurable (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (η : ℝ) :
    Measurable (Function.uncurry (cacheUpdate F R η)) := by
  let A := Cache F × (JointSpace dx dy × JointSpace dx dy)
  have hθ : Measurable (fun a : A ↦ parameter a.1) := by fun_prop
  have ha : Measurable (fun a : A ↦ anchor a.1) := by fun_prop
  have he : Measurable (fun a : A ↦ estimate a.1) := by fun_prop
  have hz : Measurable (fun a : A ↦ current a.1) := by fun_prop
  have hr1 : Measurable (fun a : A ↦ a.2.1) := by fun_prop
  have hr2 : Measurable (fun a : A ↦ a.2.2) := by fun_prop
  have hr := hR.comp (hθ.prodMk hz)
  have hη : Measurable (fun _ : A ↦ η) := measurable_const
  have hin := hz.sub (hη.smul ((he.add (hr1.sub hr2)).add hr))
  have hp := F.projection_measurable.comp (hθ.prodMk hin)
  exact (hθ.prodMk (ha.prodMk (he.prodMk hp))).subtype_mk

variable [MeasurableSpace (Fin n)]

def stepProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (η : ℝ) (k : ℕ) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Cache F)
      (InnerAlgorithm.Seed n (k + 1) × Cache F) 2 :=
  OracleProgram.mapWithSeed
    (PersistentProgram.signedPair K (fun a ↦ a.1.2) (by fun_prop)
      (fun a ↦ cacheCurrent a.2) (fun a ↦ cacheAnchor a.2)
      (cacheCurrent_measurable.comp measurable_snd) (cacheAnchor_measurable.comp measurable_snd))
    (fun a reply ↦ cacheUpdate F R η a.2 reply)
    ((cacheUpdate_measurable F R hR η).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

def cacheProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (η : ℝ) :
    (k : ℕ) → OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Cache F)
      (InnerAlgorithm.Seed n k × Cache F) (2 * k)
  | 0 => OracleProgram.pure Prod.snd measurable_snd
  | k + 1 => OracleProgram.castBudget
      (OracleProgram.bind
        (OracleProgram.withSeed (cacheProgram F R hR η k)
          (fun a : InnerAlgorithm.Seed n (k + 1) × Cache F ↦ (a.1.1, a.2)) (by fun_prop))
        (OracleProgram.withSeed (stepProgram F R hR η k)
          (fun a : (InnerAlgorithm.Seed n (k + 1) × Cache F) × Cache F ↦ (a.1.1, a.2))
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))) (by omega)

def cacheIterate {F : DomainFamily (dx := dx) K Θ}
    (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (η : ℝ) :
    (k : ℕ) → InnerAlgorithm.Seed n k → Cache F → Cache F
  | 0, _, s => s
  | k + 1, ω, s =>
      let s' := cacheIterate G R η k ω.1 s
      cacheUpdate F R η s' (G ω.2 (current s'), G ω.2 (anchor s'))

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter}

set_option backward.isDefEq.respectTransparency false in
theorem eval_stepProgram [MeasurableSpace (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (η : ℝ) (k : ℕ)
    (ω : InnerAlgorithm.Seed p.n (k + 1)) (s : Cache F) :
    OracleProgram.eval (stepProgram F R hR η k) (oracleResponse P) (ω, s) =
      cacheUpdate F R η s (signedComponentGradient P ω.2 (current s),
        signedComponentGradient P ω.2 (anchor s)) := by
  rw [stepProgram, OracleProgram.eval_mapWithSeed, PersistentProgram.eval_signedPair]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_cacheProgram [MeasurableSpace (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (η : ℝ)
    (k : ℕ) (ω : InnerAlgorithm.Seed p.n k) (s : Cache F) :
    OracleProgram.eval (cacheProgram F R hR η k) (oracleResponse P) (ω, s) =
      cacheIterate (signedComponentGradient P) R η k ω s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cacheProgram, OracleProgram.eval_castBudget, OracleProgram.eval_bind,
      OracleProgram.eval_withSeed, ih]
    rw [eval_stepProgram]
    rfl

end NCConcave16991.SVRGProgram

