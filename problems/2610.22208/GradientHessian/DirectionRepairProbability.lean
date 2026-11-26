import GradientHessian.DirectionFamilyContainment
import GradientHessian.RawFactorSeed
import GradientHessian.FactoredGeometricTests

/-! Source sphere bounds for actual adaptive direction shadows. The query
arrays are constructed from the saved-state driver and the original raw
external factor, so no independent-advice or stopped-list hypothesis occurs. -/

noncomputable section
namespace GradientHessian.DirectionFamilies
open Classical MeasureTheory HigherHierarchy HierarchyAddresses RawHierarchy
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  RawDirection DirectionPolicyReplay DirectionVisibleQueries

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (Ordinary d J E H t)] [∀ t,BorelSpace (Ordinary d J E H t)]
  [∀ t,MeasurableSpace (Rich d J E H t)] [∀ t,BorelSpace (Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]

theorem center_cap (h depth : ℕ) (w : Word depth) :
    cap (J := J) (ell := ell) (h+1+depth) (CensoredDirection.addressedNode (h+1) depth w)=
      8^(h+2)*(4096*J^2+1)*ell := by
  simp only [cap,CensoredDirection.addressedNode]
  have he : h+1+depth+1-depth=h+2 := by omega
  rw [he]

theorem old_cap (depth : ℕ) (w : Word depth) :
    cap (J := J) (ell := ell) (0+depth) (CensoredDirection.addressedNode 0 depth w)=
      8*(4096*J^2+1)*ell := by
  simp [cap,CensoredDirection.addressedNode]

theorem inner_cap (depth : ℕ) (w : Word depth) (i : Fin 8) :
    cap (J := J) (ell := ell) (0+depth) (leafNode (leafEquiv (0+depth) (prependSlot 0 depth w i)))=
      (4096*J^2+1)*ell := by
  simp [cap,leafNode]

theorem center_shadow_probability (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (policy : Machine.Policy Seed S (Point d J E H (h+1+depth))
      (Ordinary d J E H (h+1+depth)) (Rich d J E H (h+1+depth)))
    (hdim : 2≤Module.finrank ℝ (H h)) {K : ℝ} (hK : 16≤K) (N fuel : ℕ)
    (s₀ : State (h+1+depth+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (h+1+depth)).prod σ).real
      {x | hitBy P B fallback (h+1+depth) (embed (h+1) depth w (.inr i)) (centerStop h depth w i) policy K N fuel s₀ x} ≤
        (8^(h+2)*(4096*J^2+1)*ell : ℕ)*
          (2*(6*width (4096*J^2) h/radius (4096*J^2) K h)^(Module.finrank ℝ (H h)-1)) := by
  have hK0 : 0<K := by linarith
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P (h+1+depth)
  letI := RawCenterFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P h depth
  let e₀ := RawCenterFactor.factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w i
  have he := RawFactorSeed.factor_preserving e₀ (RawHierarchy.law P (h+1+depth))
    (SphereGaussian.sphereLaw (H h)) (RawCenterFactor.restLaw P h depth) σ
    (RawCenterFactor.factor_preserving P h depth w i)
  have hb := FactoredTests.center_list_bound hdim (RawFactorSeed.factor e₀) ((RawHierarchy.law P (h+1+depth)).prod σ)
    ((RawCenterFactor.restLaw P h depth).prod σ) he
    (cap (J := J) (ell := ell) (h+1+depth) (CensoredDirection.addressedNode (h+1) depth w))
    (radius_pos (4096*J^2) hK0 h) (width_pos (4096*J^2) h).le (scale_separation (4096*J^2) hK h)
    (centerQuery (n := n) P B fallback h depth w i policy K N fuel s₀)
    (centerQuery_measurable (n := n) P B fallback h depth w i policy hK0 N fuel s₀)
  have hm := measureReal_mono (μ := (RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (h+1+depth)).prod σ)
    (fun x hx => center_covered P B fallback h depth w i policy hK0 N fuel s₀ hs hell x hx)
  exact hm.trans (by simpa only [RawFactorSeed.factor_apply,e₀,center_cap] using hb)

theorem old_shadow_probability [Nontrivial E] (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (policy : Machine.Policy Seed S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth)) (Rich d J E H (0+depth)))
    {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : State (0+depth+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)).prod σ).real
      {x | hitBy P B fallback (0+depth) (embed 0 depth w (.inl (i,j))) (oldStop depth w i) policy K N fuel s₀ x} ≤
        (8*(4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)
  letI := RawMemoryHierarchyFactor.oldRestLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P depth
  let e₀ := RawMemoryHierarchyFactor.oldFactor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) depth w i j
  have he := RawFactorSeed.factor_preserving e₀ (RawHierarchy.law P (0+depth)) (SphereGaussian.sphereLaw E)
    (RawMemoryHierarchyFactor.oldRestLaw P depth) σ (RawMemoryHierarchyFactor.oldFactor_preserving P depth w i j)
  have hb := FactoredTests.memory_list_bound (RawFactorSeed.factor e₀) ((RawHierarchy.law P (0+depth)).prod σ)
    ((RawMemoryHierarchyFactor.oldRestLaw P depth).prod σ) he
    (cap (J := J) (ell := ell) (0+depth) (CensoredDirection.addressedNode 0 depth w))
    (Inner.radius (FirstHeight.depth (4096*J^2+1)) j)
    (oldQuery (n := n) P B fallback depth w i j policy K N fuel s₀)
    (oldQuery_measurable (n := n) P B fallback depth w i j policy hK N fuel s₀)
  have hm := measureReal_mono (μ := (RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)).prod σ)
    (fun x hx => old_covered P B fallback depth w i j policy hK N fuel s₀ hs hell x hx)
  exact hm.trans (by simpa only [RawFactorSeed.factor_apply,e₀,old_cap] using hb)

theorem inner_shadow_probability [Nontrivial E] (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (policy : Machine.Policy Seed S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth)) (Rich d J E H (0+depth)))
    {K : ℝ} (hK : 0<K) (N fuel : ℕ) (s₀ : State (0+depth+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)).prod σ).real
      {x | hitBy P B fallback (0+depth) (embed 0 depth w (.inr (i,j,k)))
        (taskDisclosed (leafEquiv (0+depth) (prependSlot 0 depth w i)) j) policy K N fuel s₀ x} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)
  letI := RawMemoryHierarchyFactor.innerRestLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P depth
  let e₀ := RawMemoryHierarchyFactor.innerFactor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) depth w i j k
  have he := RawFactorSeed.factor_preserving e₀ (RawHierarchy.law P (0+depth)) (SphereGaussian.sphereLaw E)
    (RawMemoryHierarchyFactor.innerRestLaw P depth) σ (RawMemoryHierarchyFactor.innerFactor_preserving P depth w i j k)
  have hb := FactoredTests.memory_list_bound (RawFactorSeed.factor e₀) ((RawHierarchy.law P (0+depth)).prod σ)
    ((RawMemoryHierarchyFactor.innerRestLaw P depth).prod σ) he
    (cap (J := J) (ell := ell) (0+depth) (leafNode (leafEquiv (0+depth) (prependSlot 0 depth w i))))
    (Inner.radius Inner.absoluteDepth k)
    (innerQuery (n := n) P B fallback depth w i j k policy K N fuel s₀)
    (innerQuery_measurable (n := n) P B fallback depth w i j k policy hK N fuel s₀)
  have hm := measureReal_mono (μ := (RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+depth)).prod σ)
    (fun x hx => inner_covered P B fallback depth w i j k policy hK N fuel s₀ hs hell x hx)
  exact hm.trans (by simpa only [RawFactorSeed.factor_apply,e₀,inner_cap] using hb)

end GradientHessian.DirectionFamilies
