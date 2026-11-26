import Bilevel.MultiscaleDisclosedIngredients

/-! Explicit old/new scalar potentials for the macro-free original SFO.
No undisclosed frame, completion, or inverse appears in these formulas. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped Topology RealInnerProductSpace
namespace Bilevel.MultiscaleMean
open ZeroChain ZeroChainSchedule CompensatedMean SmallGapProfiles
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E:=E) n)

theorem perturbation_flat_formula (y : LowerSpace E) :
    P.data.perturbation y=P.μ/(2*P.L^2)*P.residual (uProj E y)^2-
      P.μ/P.L*(P.residual (uProj E y)*normal P.finalWidth (sProj E y)+
        ∑ j ∈ Finset.range (levels P.θ),P.flatApproximation j (uProj E y)*
          (normal (width P.c P.β P.θ j) (sProj E y)-normal (width P.c P.β P.θ (j+1)) (sProj E y))) := by
  have hh := P.inactivePerturbation_flat_formula y
  simp only [inactivePerturbation,signal,residualDifference] at hh
  linarith

def disclosedPerturbation (active : Bool) (r : ℕ) (columns : Fin (n+1) → E) (y : LowerSpace E) : ℝ :=
  let z := if active then P.disclosedResidual r columns (uProj E y)
    else P.disclosedFlat P.signalResolution r columns (uProj E y)
  P.μ/(2*P.L^2)*z^2-P.μ/P.L*(z*normal P.finalWidth (sProj E y)+
    ∑ j ∈ Finset.range (levels P.θ),P.disclosedFlat (resolution P.c P.β P.θ j) r columns (uProj E y)*
      (normal (width P.c P.β P.θ j) (sProj E y)-normal (width P.c P.β P.θ (j+1)) (sProj E y)))

def disclosedUpper (r : ℕ) (columns : Fin (n+1) → E) (_x : E) (y : LowerSpace E) : ℝ :=
  P.disclosedRevealed r columns (uProj E y)+P.L*sProj E y

def quadraticPart (x : E) (y : LowerSpace E) : ℝ :=
  P.μ/2*(‖uProj E y‖^2+(sProj E y)^2)+P.L/2*(zProj E y)^2-P.L*⟪x,uProj E y⟫

def disclosedLower (active : Bool) (r : ℕ) (columns : Fin (n+1) → E) (x : E) (y : LowerSpace E) : ℝ :=
  P.quadraticPart x y+P.disclosedPerturbation active r columns y

theorem approximation_disclosed_all (r s : ℕ) (hrs : r≤s) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<s → columns k=P.U (basis k))
    (y : LowerSpace E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n P.R P.U (uProj E y) k|<P.signalResolution) :
    ∀ᶠ z in 𝓝 y,∀ j∈Finset.range (levels P.θ),
      P.flatApproximation j (uProj E z)=P.disclosedFlat (resolution P.c P.β P.θ j) s columns (uProj E z) := by
  apply (Filter.eventually_all_finset _).mpr
  intro j hj
  exact (P.approximation_disclosed_germ j (Finset.mem_range.mp hj) r s hrs columns hcols _ hu).comp_tendsto
    (uProj E).continuous.continuousAt

theorem active_lower_disclosed_germ (r : ℕ) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<r+1 → columns k=P.U (basis k))
    (x : E) (y : LowerSpace E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n P.R P.U (uProj E y) k|<P.signalResolution) :
    P.data.lower x=ᶠ[𝓝 y] P.disclosedLower true (r+1) columns x := by
  have hr := (P.residual_disclosed_germ r columns hcols _ hu).comp_tendsto
    (uProj E).continuous.continuousAt
  have ha := P.approximation_disclosed_all r (r+1) (by omega) columns hcols y hu
  filter_upwards [hr,ha] with z hz hza
  dsimp only [Function.comp_apply] at hz
  change P.quadraticPart x z+P.data.perturbation z=_
  rw [P.perturbation_flat_formula]
  simp only [disclosedLower,disclosedPerturbation,if_true,hz]
  congr 4
  apply Finset.sum_congr rfl
  intro j hj
  rw [hza j hj]

theorem inactive_lower_disclosed_germ (r : ℕ) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<r → columns k=P.U (basis k))
    (x : E) (y : LowerSpace E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n P.R P.U (uProj E y) k|<P.signalResolution) :
    P.inactiveLower x=ᶠ[𝓝 y] P.disclosedLower false r columns x := by
  have hr := (P.inactive_disclosed_germ r columns hcols _ hu).comp_tendsto
    (uProj E).continuous.continuousAt
  have ha := P.approximation_disclosed_all r r le_rfl columns hcols y hu
  filter_upwards [hr,ha] with z hz hza
  dsimp only [Function.comp_apply] at hz
  have he : P.inactiveLower x z=P.quadraticPart x z+P.inactivePerturbation z := by
    simp only [inactiveLower,inactivePerturbation,CompensatedMean.Data.lower,data,quadraticPart]
    ring
  rw [he,P.inactivePerturbation_flat_formula]
  simp only [disclosedLower,disclosedPerturbation,Bool.false_eq_true,if_false,hz]
  congr 4
  apply Finset.sum_congr rfl
  intro j hj
  rw [hza j hj]

theorem upper_disclosed_germ (r : ℕ) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<r → columns k=P.U (basis k))
    (x : E) (y : LowerSpace E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n P.R P.U (uProj E y) k|<P.signalResolution) :
    P.data.upper x=ᶠ[𝓝 y] P.disclosedUpper r columns x := by
  have hh := (P.revealed_disclosed_germ r columns hcols _ hu).comp_tendsto
    (uProj E).continuous.continuousAt
  filter_upwards [hh] with z hz
  exact congrArg (fun t => t+P.L*sProj E z) hz

end Parameters
end Bilevel.MultiscaleMean
