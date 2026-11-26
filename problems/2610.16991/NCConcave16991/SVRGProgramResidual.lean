import NCConcave16991.SVRGProgramEpoch

/-! # Two full passes compute the actual projected normal-cone residual -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.SVRGProgram

variable {n dx dy : ℕ} {D : ℝ} {K : KnownDualDomain dy D}
  {Θ : Type*} [MeasurableSpace Θ]

abbrev Forward (F : DomainFamily (dx := dx) K Θ) :=
  {a : Θ × JointSpace dx dy × JointSpace dx dy × JointSpace dx dy //
    a.2.1 ∈ F.carrier a.1 ∧ a.2.2.1 ∈ F.carrier a.1}

/-- Parameter, projected feasible point, computed normal, and computed residual. -/
abbrev Result (F : DomainFamily (dx := dx) K Θ) :=
  {a : Θ × JointSpace dx dy × JointSpace dx dy × JointSpace dx dy //
    a.2.1 ∈ F.carrier a.1}

def forwardPoint {F : DomainFamily (dx := dx) K Θ} (s : Forward F) : Point F :=
  ⟨(s.1.1, s.1.2.2.1), s.2.2⟩

theorem forwardPoint_measurable {F : DomainFamily (dx := dx) K Θ} :
    Measurable (forwardPoint (F := F)) := by
  apply Measurable.subtype_mk
  exact (measurable_fst.comp measurable_subtype_coe).prodMk
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_subtype_coe)))

def forwardUpdate (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (ell : ℝ)
    (point : Point F) (mean : JointSpace dx dy) : Forward F :=
  let Tz := mean + R (point.1.1, point.1.2)
  let zplus := VariationalInequality.projection (F.carrier point.1.1)
    (F.nonempty _) (F.closed _) (F.convex _) (point.1.2 - ell⁻¹ • Tz)
  ⟨(point.1.1, point.1.2, (zplus : JointSpace dx dy),
      ell • (point.1.2 - (zplus : JointSpace dx dy)) - Tz), ⟨point.2, zplus.2⟩⟩

theorem forwardUpdate_measurable (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (ell : ℝ) :
    Measurable (Function.uncurry (forwardUpdate F R ell)) := by
  let A := Point F × JointSpace dx dy
  have hθ : Measurable (fun a : A ↦ a.1.1.1) := by fun_prop
  have hz : Measurable (fun a : A ↦ a.1.1.2) := by fun_prop
  have hT := measurable_snd.add (hR.comp (hθ.prodMk hz))
  have hi : Measurable (fun _ : A ↦ ell⁻¹) := measurable_const
  have he : Measurable (fun _ : A ↦ ell) := measurable_const
  have hp := F.projection_measurable.comp (hθ.prodMk (hz.sub (hi.smul hT)))
  have hn := (he.smul (hz.sub hp)).sub hT
  exact (hθ.prodMk (hz.prodMk (hp.prodMk hn))).subtype_mk

def finishUpdate (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (s : Forward F)
    (mean : JointSpace dx dy) : Result F :=
  ⟨(s.1.1, s.1.2.2.1, s.1.2.2.2,
    mean + R (s.1.1, s.1.2.2.1) + s.1.2.2.2), s.2.2⟩

theorem finishUpdate_measurable (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) :
    Measurable (Function.uncurry (finishUpdate F R)) := by
  let A := Forward F × JointSpace dx dy
  have hθ : Measurable (fun a : A ↦ a.1.1.1) := by fun_prop
  have hp : Measurable (fun a : A ↦ a.1.1.2.2.1) := by fun_prop
  have hn : Measurable (fun a : A ↦ a.1.1.2.2.2) := by fun_prop
  exact (hθ.prodMk (hp.prodMk (hn.prodMk
    ((measurable_snd.add (hR.comp (hθ.prodMk hp))).add hn)))).subtype_mk

variable [MeasurableSpace (Fin n)]

def forwardProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (ell : ℝ) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Forward F) (Point F) n :=
  OracleProgram.mapWithSeed
    (PersistentProgram.fullSignedPass K originalPoint originalPoint_measurable)
    (forwardUpdate F R ell) (forwardUpdate_measurable F R hR ell)

def finishProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Result F) (Forward F) n :=
  OracleProgram.mapWithSeed
    (PersistentProgram.fullSignedPass K (fun s ↦ originalPoint (forwardPoint s))
      (originalPoint_measurable.comp forwardPoint_measurable))
    (finishUpdate F R) (finishUpdate_measurable F R hR)

def residualProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (ell : ℝ) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Result F) (Point F) (2 * n) :=
  OracleProgram.castBudget
    (OracleProgram.bind (forwardProgram F R hR ell)
      (OracleProgram.withSeed (finishProgram F R hR) Prod.snd measurable_snd)) (by omega)

def directForward (F : DomainFamily (dx := dx) K Θ)
    (T : Θ → JointSpace dx dy → JointSpace dx dy) (ell : ℝ) (point : Point F) : Forward F :=
  let z : F.carrier point.1.1 := ⟨point.1.2, point.2⟩
  let zplus := SVRG.fullStep (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _) (T point.1.1) ell z
  ⟨(point.1.1, point.1.2, (zplus : JointSpace dx dy),
      SVRG.fullStepNormal (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _) (T point.1.1) ell z),
    ⟨point.2, zplus.2⟩⟩

def directResult (F : DomainFamily (dx := dx) K Θ)
    (T : Θ → JointSpace dx dy → JointSpace dx dy) (ell : ℝ) (point : Point F) : Result F :=
  let z : F.carrier point.1.1 := ⟨point.1.2, point.2⟩
  let zplus := SVRG.fullStep (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _) (T point.1.1) ell z
  ⟨(point.1.1, (zplus : JointSpace dx dy),
      SVRG.fullStepNormal (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _) (T point.1.1) ell z,
      SVRG.fullStepResidual (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _) (T point.1.1) ell z),
    zplus.2⟩

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter}

set_option backward.isDefEq.respectTransparency false in
theorem eval_forwardProgram [MeasurableSpace (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (ell : ℝ) (point : Point F) :
    OracleProgram.eval (forwardProgram F R hR ell) (oracleResponse P) point =
      directForward F (fun θ ↦ averageMap (fun i z ↦ signedComponentGradient P i z + R (θ, z))) ell point := by
  rw [forwardProgram, OracleProgram.eval_mapWithSeed, PersistentProgram.eval_fullSignedPass]
  have hT : (fun θ ↦ averageMap (fun i z ↦ signedComponentGradient P i z + R (θ, z))) =
      (fun θ z ↦ averageMap (signedComponentGradient P) z + R (θ, z)) := by
    funext θ z
    exact averageMap_add_known p.n_pos _ _ z
  rw [hT]
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_finishProgram [MeasurableSpace (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (s : Forward F) :
    OracleProgram.eval (finishProgram F R hR) (oracleResponse P) s =
      finishUpdate F R s (averageMap (signedComponentGradient P) s.1.2.2.1) := by
  rw [finishProgram, OracleProgram.eval_mapWithSeed, PersistentProgram.eval_fullSignedPass]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_residualProgram [MeasurableSpace (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (ell : ℝ) (point : Point F) :
    OracleProgram.eval (residualProgram F R hR ell) (oracleResponse P) point =
      directResult F (fun θ ↦ averageMap (fun i z ↦ signedComponentGradient P i z + R (θ, z))) ell point := by
  rw [residualProgram, OracleProgram.eval_castBudget, OracleProgram.eval_bind,
    OracleProgram.eval_withSeed, eval_forwardProgram, eval_finishProgram]
  have hT : (fun θ ↦ averageMap (fun i z ↦ signedComponentGradient P i z + R (θ, z))) =
      (fun θ z ↦ averageMap (signedComponentGradient P) z + R (θ, z)) := by
    funext θ z
    exact averageMap_add_known p.n_pos _ _ z
  rw [hT]
  apply Subtype.ext
  rfl

end NCConcave16991.SVRGProgram
