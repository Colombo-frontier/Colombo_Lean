import Nonsmooth.NestedCircularFinalRay

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The actual nested circular path supplies every hypothesis of the recursive full-space cone certificate. -/
theorem nestedCircular_full_cone_certificate (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (f : E → ℝ) (hRpos : 0 < R) (G : Set E)
    (hballG : Metric.closedBall (0 : E) R ⊆ G) (hf : ConvexOn ℝ G f)
    (D : ℕ) (hD : 0 < D) (hDim : D ≤ Module.finrank ℝ E - 1)
    (hline : Module.finrank ℝ (nestedCircularSpace R ε N hR hε hε1 f D) = 1)
    (hθ : 2 / (2 : ℝ) ^ N ≤ ε / 2) :
    comparisonConeExcluded G f ⊤
      (nestedCircularApex R ε N hR hε hε1 f D) (nestedCircularRadial R ε N hR hε hε1 f (D - 1))
      (coneLiftCoefficient ε D) (f (nestedCircularApex R ε N hR hε hε1 f D)) := by
  let K := nestedCircularSpace R ε N hR hε hε1 f
  let x := nestedCircularApex R ε N hR hε hε1 f D
  let e := nestedCircularRadial R ε N hR hε hε1 f (D - 1)
  have he : ‖e‖ = 1 := nestedCircularRadial_unit R ε N hR hε hε1 f (D - 1) (by omega)
  have heK : e ∈ K D := by
    have h := nestedCircularRadial_mem_next R ε N hR hε hε1 f (D - 1) (by omega)
    simpa only [Nat.sub_add_cancel (show 1 ≤ D by omega)] using h
  have hbase : comparisonConeExcluded G f (K D) x e 0 (f x) :=
    nestedCircular_final_line_cone R ε N hR hε hε1 f hRpos G hballG hf D hD hDim hline
  have hlifts (m : ℕ) (hm : m ≤ D) :
      comparisonConeExcluded G f (K (D - m)) x e (coneLiftCoefficient ε m) (f x) := by
    induction m with
    | zero => simpa only [Nat.sub_zero, coneLiftCoefficient] using hbase
    | succ m ih =>
      have hmD : m < D := by omega
      let i := D - (m + 1)
      have hiD : i < D := by dsimp [i]; omega
      have hip : i + 1 = D - m := by dsimp [i]; omega
      have hi1D : i + 1 ≤ D := by omega
      have hi := ih (by omega)
      let w := nestedCircularOffset R ε N hR hε hε1 f D i
      let n := nestedCircularNormal R ε N hR hε hε1 f i
      let a := shrinkingCircularRadius R ε N i * Real.sin (circularGridAngle N)
      obtain ⟨ha, hnK, hn, hwK, hw, hqm, hqp, hfm, hfp⟩ :=
        nestedCircular_pair_certificate R ε N hR hε hε1 f hRpos D i hiD hDim hθ
      have hflag : K (i + 1) = K i ⊓ (ℝ ∙ n)ᗮ := nestedCircularSpace_orthogonal_flag R ε N hR hε hε1 f i
      have heH : e ∈ K i ⊓ (ℝ ∙ n)ᗮ := by
        rw [← hflag]
        exact (nestedCircularSpace_antitone R ε N hR hε hε1 f hi1D) heK
      have hwH : w ∈ K i ⊓ (ℝ ∙ n)ᗮ := by rw [← hflag]; exact hwK
      have hsection : comparisonConeExcluded G f (K i ⊓ (ℝ ∙ n)ᗮ)
          x e (coneLiftCoefficient ε m) (f x) := by
        rw [← hflag, hip]
        exact hi
      exact comparisonConeExcluded_lift hf (K i) x w n e hnK hn he heH hwH
        (coneLiftCoefficient_nonneg ε m) ha hw (hballG (by simpa using hqm))
        (hballG (by simpa using hqp)) hfm hfp hsection
  have h := hlifts D le_rfl
  simpa only [Nat.sub_self, K, (nestedCircular_initial_geometry R ε N hR hε hε1 f).2] using h

end
end Nonsmooth
