import NCConcave16991.SVRGProgramFamily

/-! # A genuine full-pass/cached projected SVRG epoch -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.SVRGProgram

variable {n dx dy : ℕ} {D : ℝ} {K : KnownDualDomain dy D}
  {Θ : Type*} [MeasurableSpace Θ]

def initializeCache {F : DomainFamily (dx := dx) K Θ} (point : Point F)
    (mean : JointSpace dx dy) : Cache F :=
  ⟨(point.1.1, point.1.2, mean, point.1.2), ⟨point.2, point.2⟩⟩

theorem initializeCache_measurable {F : DomainFamily (dx := dx) K Θ} :
    Measurable (Function.uncurry (initializeCache (F := F))) := by
  have hθ : Measurable (fun a : Point F × JointSpace dx dy ↦ a.1.1.1) := by fun_prop
  have hz : Measurable (fun a : Point F × JointSpace dx dy ↦ a.1.1.2) := by fun_prop
  exact (hθ.prodMk (hz.prodMk (measurable_snd.prodMk hz))).subtype_mk

variable [MeasurableSpace (Fin n)]

def initializeProgram (F : DomainFamily (dx := dx) K Θ) (k : ℕ) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Cache F)
      (InnerAlgorithm.Seed n k × Point F) n :=
  OracleProgram.mapWithSeed
    (PersistentProgram.fullSignedPass K (fun a ↦ originalPoint a.2)
      (originalPoint_measurable.comp measurable_snd))
    (fun a mean ↦ initializeCache a.2 mean)
    (initializeCache_measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

def epochProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (η : ℝ) (k : ℕ) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Point F)
      (InnerAlgorithm.Seed n k × Point F) (n + 2 * k) :=
  OracleProgram.map
    (OracleProgram.bind (initializeProgram F k)
      (OracleProgram.withSeed (cacheProgram F R hR η k)
        (fun a : (InnerAlgorithm.Seed n k × Point F) × Cache F ↦ (a.1.1, a.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    currentPoint currentPoint_measurable

def cacheAt {F : DomainFamily (dx := dx) K Θ} (point : Point F) (mean : JointSpace dx dy)
    (z : F.carrier point.1.1) : Cache F :=
  ⟨(point.1.1, point.1.2, mean, (z : JointSpace dx dy)), ⟨point.2, z.2⟩⟩

theorem cacheIterate_initialize {F : DomainFamily (dx := dx) K Θ}
    (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (η : ℝ) (point : Point F)
    (mean : JointSpace dx dy) (k : ℕ) (ω : InnerAlgorithm.Seed n k) :
    cacheIterate G R η k ω (initializeCache point mean) =
      cacheAt point mean (InnerAlgorithm.estimatedTrajectory
        (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
        G (fun z ↦ R (point.1.1, z)) ⟨point.1.2, point.2⟩ mean η k ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cacheIterate, ih]
    rfl

/-- A common known correction is added after the cached average of the
original component gradients; its anchor value cancels exactly. -/
theorem averageMap_add_known (hn : 0 < n)
    (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (R : JointSpace dx dy → JointSpace dx dy) (z : JointSpace dx dy) :
    averageMap (fun i w ↦ G i w + R w) z = averageMap G z + R z := by
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [averageMap, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_add]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hnr, one_smul]

theorem estimator_add_known (hn : 0 < n)
    (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (R : JointSpace dx dy → JointSpace dx dy) (a z : JointSpace dx dy) (i : Fin n) :
    InnerAlgorithm.estimator G R a 0 z i =
      InnerAlgorithm.estimator (fun j w ↦ G j w + R w) (fun _ ↦ 0) a 0 z i := by
  simp only [InnerAlgorithm.estimator, averageMap_add_known hn, add_zero]
  abel

theorem trajectory_add_known (hn : 0 < n)
    (F : DomainFamily (dx := dx) K Θ) (point : Point F)
    (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (R : JointSpace dx dy → JointSpace dx dy) (η : ℝ) (k : ℕ)
    (ω : InnerAlgorithm.Seed n k) :
    InnerAlgorithm.trajectory (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
      G R ⟨point.1.2, point.2⟩ 0 η k ω =
    SVRG.epochIterate (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
      (fun i z ↦ G i z + R z) ⟨point.1.2, point.2⟩ η k ω := by
  unfold SVRG.epochIterate
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [InnerAlgorithm.trajectory, InnerAlgorithm.step, ih]
    rw [estimator_add_known hn G R]

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter}

set_option backward.isDefEq.respectTransparency false in
theorem eval_initializeProgram [MeasurableSpace (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (k : ℕ) (ω : InnerAlgorithm.Seed p.n k) (point : Point F) :
    OracleProgram.eval (initializeProgram F k) (oracleResponse P) (ω, point) =
      initializeCache point (averageMap (signedComponentGradient P) point.1.2) := by
  rw [initializeProgram, OracleProgram.eval_mapWithSeed, PersistentProgram.eval_fullSignedPass]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_epochProgram [MeasurableSpace (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R) (η : ℝ)
    (k : ℕ) (ω : InnerAlgorithm.Seed p.n k) (point : Point F) :
    OracleProgram.eval (epochProgram F R hR η k) (oracleResponse P) (ω, point) =
      ⟨(point.1.1, (SVRG.epochIterate (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
        (fun i z ↦ signedComponentGradient P i z + R (point.1.1, z))
        ⟨point.1.2, point.2⟩ η k ω : JointSpace dx dy)),
        (SVRG.epochIterate (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
        (fun i z ↦ signedComponentGradient P i z + R (point.1.1, z))
        ⟨point.1.2, point.2⟩ η k ω).2⟩ := by
  rw [epochProgram, OracleProgram.eval_map, OracleProgram.eval_bind,
    eval_initializeProgram, OracleProgram.eval_withSeed, eval_cacheProgram,
    cacheIterate_initialize]
  have ht := InnerAlgorithm.estimatedTrajectory_eq (F.carrier point.1.1)
    (F.nonempty _) (F.closed _) (F.convex _) (signedComponentGradient P)
    (fun z ↦ R (point.1.1, z)) ⟨point.1.2, point.2⟩ (0 : JointSpace dx dy) η k ω
  simp only [add_zero] at ht
  rw [ht, trajectory_add_known p.n_pos F point]
  rfl

end NCConcave16991.SVRGProgram
