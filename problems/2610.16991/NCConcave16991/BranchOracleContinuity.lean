import NCConcave16991.BranchOracleGlobal
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Joint continuity and measurable public outer derivatives -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard LocalizationScalar LocalizationRadial
open scoped BigOperators InnerProductSpace

variable {A E X : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]

theorem outerStage_continuous_family (u : X → A) (v s b : X → E) (a : X → A) (previous : X → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hs : Continuous s) (hb : Continuous b)
    (ha : Continuous a) (hp : Continuous previous) :
    Continuous (fun x ↦ outerStage (u x) (v x) (previous x) (s x) (a x) (b x)) := by
  have hcapS := (radialCap_contDiff (by norm_num : (0 : ℝ) < 10)).continuous.comp hs
  have ht : Continuous (fun x ↦ stateScore (v x) (s x)) := hv.inner hcapS
  have hgprev := gate_contDiff.continuous.comp hp
  have hgcur := gate_contDiff.continuous.comp ht
  have hload : Continuous (fun x ↦ activationLoad (previous x) (stateScore (v x) (s x))) :=
    hgprev.mul (continuous_const.sub hgcur)
  have hentry : Continuous (fun x ↦ ⟪u x, radialCap 21 (a x)⟫_ℝ) :=
    hu.inner ((radialCap_contDiff (by norm_num : (0 : ℝ) < 21)).continuous.comp ha)
  have hexit : Continuous (fun x ↦ ⟪radialCap 10 (s x), radialCap 21 (b x)⟫_ℝ) :=
    hcapS.inner ((radialCap_contDiff (by norm_num : (0 : ℝ) < 21)).continuous.comp hb)
  have hen := ((continuous_const (y := (-4 : ℝ))).mul hload).mul hentry
  have hxit := hload.neg.mul hexit
  have hpreFactor : Continuous precedingFactor :=
    ((continuous_const.sub stateClamp_contDiff.continuous).mul (continuous_const.sub gate_contDiff.continuous))
  have hcoup := ((continuous_const (y := stateWeight)).mul hgcur).mul (hpreFactor.comp hp)
  have hpen := (((continuous_const (y := gamma / 2)).mul (hs.norm.pow 2)).sub
    ((continuous_const (y := gamma / 2)).mul (activationSq_contDiff.continuous.comp ht))).add
      (statePotential_contDiff.continuous.comp ht)
  exact ((hen.add hxit).add hcoup).add hpen

variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

abbrev SourceParameters := (∀ j, V j 0) × (∀ j, V j (Fin.last N))

theorem precedingScore_joint_continuous (j : Fin M) :
    Continuous (fun q : SourceParameters V × GlobalHard.Joint V ↦ precedingScore V q.1.2 j q.2) := by
  unfold precedingScore
  generalize j.castSucc = k
  refine Fin.cases continuous_const (fun k ↦ ?_) k
  change Continuous (fun q : SourceParameters V × GlobalHard.Joint V ↦
    ⟪q.1.2 k, radialCap 10 (stateProj V k q.2)⟫_ℝ)
  exact ((continuous_apply k).comp continuous_fst.snd).inner
    ((radialCap_contDiff (by norm_num : (0 : ℝ) < 10)).continuous.comp ((stateProj V k).continuous.comp continuous_snd))

theorem outerPublic_joint_continuous :
    Continuous (fun q : SourceParameters V × GlobalHard.Joint V ↦ outerPublic V q.1.1 q.1.2 q.2) := by
  unfold outerPublic
  apply continuous_finset_sum
  intro j _
  exact outerStage_continuous_family _ _ _ _ _ _
    ((continuous_apply j).comp continuous_fst.fst) ((continuous_apply j).comp continuous_fst.snd)
    ((stateProj V j).continuous.comp continuous_snd) ((bProj V j).continuous.comp continuous_snd)
    ((aProj V j).continuous.comp continuous_snd) (precedingScore_joint_continuous V j)

variable [LocallyCompactSpace (GlobalHard.Joint V)]
  [MeasurableSpace (SourceParameters V)] [OpensMeasurableSpace (SourceParameters V)]
  [MeasurableSpace (GlobalHard.Joint V)] [OpensMeasurableSpace (GlobalHard.Joint V)]

/-- The derivative used by the renderer is jointly measurable in all released
sources and the complete unrestricted query point. -/
theorem outerPublic_fderiv_measurable :
    Measurable (fun q : SourceParameters V × GlobalHard.Joint V ↦ fderiv ℝ (outerPublic V q.1.1 q.1.2) q.2) :=
  measurable_fderiv_with_param ℝ (f := fun p : SourceParameters V ↦ outerPublic V p.1 p.2)
    (outerPublic_joint_continuous V)

end
end NCConcave16991.BranchOracle
