import GradientHessian.AugmentedNumericalPreTransparency
import GradientHessian.AugmentedNumericalPostEndpoint
import GradientHessian.AugmentedNumericalProbability
import GradientHessian.NumericalSourceHit

noncomputable section
namespace GradientHessian.AugmentedNumericalCompiledEndpoint
open Classical Matrix HigherHierarchy HierarchyAddresses FrontierState TaskState TaskSlots
  ComparisonController ComparisonControllerReplay GeometricRepair ControllerNormalRealization NumericalSourceCaches
open scoped InnerProductSpace

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
  (DirectionPolicyReplay.Point d J E H t)
  (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

theorem rawEvent_of_endpoint {K : ℝ} (hK : 0<K) (hell : 0<ell)
    (x : RawHierarchy.Raw d n r J E H t × Seed) (N : ℕ) (j : Fin (4096*J^2+1))
    (k steps rem : ℕ) (a : S) (output : Bool)
    (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t))
    (u : State (t+1) (4096*J^2+1) ell) :
    let w := input t leaf j x
    let A := ForkMachineBound.sourceA J P w
    let readout := ForkMachineBound.earlierReadout J P fallback w
    let saved := AugmentedNumericalPreTransparency.savedRuntime.{_,_,1} P B fallback t leaf policy K j A readout N w.1.2 k
    let branch := AugmentedNumericalPostprocessor.initial t saved w.2.1
    Ready (AugmentedNumericalDriver.state t saved.2.2) →
    AugmentedNumericalCursorInvariant.coherent (taskDisclosed leaf j) saved.2.2 →
    TaskState.current (AugmentedNumericalDriver.state t saved.2.2)=some leaf →
    ((AugmentedNumericalDriver.state t saved.2.2).completed leaf).val=j.val →
    AugmentedNumericalDriver.finished t saved.2.2=false →
    AugmentedNumericalPostEndpoint.unguarded t P B fallback leaf policy K N j A branch steps=
      Sum.inr (.pending rem a output (.normal p u)) →
    IsEarlyFor (rules K (RawHierarchy.assemble P B fallback t x.1)) p u (leaf,j) →
    taskDisclosed leaf j u=false →
    x∈AugmentedNumericalProbability.rawEvent P B fallback t leaf policy hK j N := by
  intro w A readout saved branch hsready hscoherent hscurrent hsindex hsfinished hres hearly hstop
  have hsupply : AugmentedDisclosure.markStop leaf j (AugmentedNumericalDriver.state t saved.2.2)=true :=
    decide_eq_true (Or.inr ⟨hscurrent,hsindex.symm⟩)
  have hshalt : AugmentedNumericalPreprocessor.halt t leaf j saved=true := by
    simp [AugmentedNumericalPreprocessor.halt,hsupply]
  obtain ⟨fuel,hmode,htest⟩ := AugmentedNumericalPostEndpoint.selected_of_unguarded_normal
    t P B fallback leaf policy hK hell N j A branch rfl hsready hscoherent hscurrent hsindex
    steps rem a output p u hres hearly.2.2.1 hstop
  have hcapstate := AugmentedNumericalPreTransparency.capped_state P B fallback t leaf policy hK hell j A readout N w.1.2 k
  have hcapflag := AugmentedNumericalPreTransparency.capped_halted P B fallback t leaf policy hK hell j A readout N w.1.2 k hshalt
  have hhit := hit_readout P B fallback t leaf (K := K) x j p u hearly.1 hearly.2.1 hearly.2.2.2.1
  change w∈AugmentedNumericalProbability.forkEvent P B fallback t leaf policy hK j N
  refine ⟨j.val+k,hcapflag,?_,fuel,?_,?_⟩
  · change AugmentedNumericalPostprocessor.enabled t leaf j
      (((AugmentedNumericalForkPrograms.pre t P B fallback leaf policy hK N j).eval A readout (j.val+k)
        ((AugmentedNumericalForkPrograms.preInitial (d := d) (n := n) (r := r) (J := J) (ell := ell)
          (E := E) (H := H) (Seed := Seed) (S := S) t j ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w.1.2)).2.1.1)=true
    rw [hcapstate]
    exact decide_eq_true ⟨hsfinished,hscurrent,hsindex⟩
  · change (AugmentedNumericalPostprocessor.cappedProgram t P B fallback leaf policy hK N j).mode
      ((AugmentedNumericalPostprocessor.cappedProgram t P B fallback leaf policy hK N j).run A fuel
        (AugmentedNumericalPostprocessor.initial t
          (((AugmentedNumericalForkPrograms.pre t P B fallback leaf policy hK N j).eval A readout (j.val+k)
            ((AugmentedNumericalForkPrograms.preInitial (d := d) (n := n) (r := r) (J := J) (ell := ell)
              (E := E) (H := H) (Seed := Seed) (S := S) t j ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w.1.2)).2.1.1)
          w.2.1,ell+1,ell+3))=3
    rw [hcapstate]
    exact hmode
  · change ForkLifetime.gamma < |⟪UnmarkedReadout.sourceOutput J P w.1.1 B fallback w.2.1,
      (AugmentedNumericalPostprocessor.cappedProgram t P B fallback leaf policy hK N j).test
        ((AugmentedNumericalPostprocessor.cappedProgram t P B fallback leaf policy hK N j).run A fuel
          (AugmentedNumericalPostprocessor.initial t
            (((AugmentedNumericalForkPrograms.pre t P B fallback leaf policy hK N j).eval A readout (j.val+k)
              ((AugmentedNumericalForkPrograms.preInitial (d := d) (n := n) (r := r) (J := J) (ell := ell)
                (E := E) (H := H) (Seed := Seed) (S := S) t j ((4096*J^2+1)*ell+1) (4096*J^2+1)).1 w.1.2)).2.1.1)
            w.2.1,ell+1,ell+3))⟫_ℝ|
    rw [hcapstate,htest]
    exact hhit

end GradientHessian.AugmentedNumericalCompiledEndpoint
