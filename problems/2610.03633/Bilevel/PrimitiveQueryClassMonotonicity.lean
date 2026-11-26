import Bilevel.PrimitiveQueryFamily

/-! Enlarging the actual admissible class can only increase its minimax
complexity, including the accuracy constraint on the solver. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
set_option autoImplicit false
variable {μ L ρ Δ R₀ σf σg : ℝ}

theorem complexity_mono_class
    (C C' : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ)
    (hCC' : ∀ G I,C G I → C' G I) : Complexity C ε≤Complexity C' ε := by
  unfold Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  refine (iInf_le _ ⟨A.val,fun G I hI => A.property G I (hCC' G I hI)⟩).trans ?_
  apply iSup_le
  intro I
  exact le_iSup_of_le ⟨I.val,hCC' I.val.1 I.val.2 I.property⟩ le_rfl

theorem conservative_curvature_complexity_le (Λ ε : ℝ) :
    Complexity (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε≤
    Complexity (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε :=
  complexity_mono_class _ _ ε (fun _ _ h => h.2)

end Bilevel.PrimitiveQuery
