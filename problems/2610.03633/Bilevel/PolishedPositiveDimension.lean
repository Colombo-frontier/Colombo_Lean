import Bilevel.PrimitiveQueryFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Restricting the stationary hardness model to the strictly positive
dimensions in the paper. A zero dimensional outer space admits a genuine
zero-call solver, so it cannot witness a strictly positive lower bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedPositiveDimension
open PrimitiveQuery BorelAdaptive

def zeroAlgorithm (G : Geometry) : Algorithm G where
  Private := Unit
  State := Unit
  privateLaw := Measure.dirac ()
  program := {
    query := fun _ => 0
    query_measurable := measurable_const
    update := fun _ => ()
    update_measurable := measurable_const
    halt := fun _ => true
    halt_measurable := measurable_const
    output := fun _ => 0
    output_measurable := measurable_const }
  start := fun _ => ()
  start_measurable := measurable_const

theorem zeroAlgorithm_totalCalls (G : Geometry) {Seed : Type*}
    (response : Unit → G.Query → Seed → G.Reply)
    (p : Sample Unit Unit Seed) :
    totalCalls (zeroAlgorithm G).program response p=0 := by
  rw [totalCalls_eq_iSup_calls]
  have hc (n : ℕ) : calls (zeroAlgorithm G).program response p.1 p.2.2 p.2.1 n=0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change calls (zeroAlgorithm G).program response p.1 p.2.2 p.2.1 n+
        (if true then 0 else 1)=0
      simp only [if_true,add_zero,ih]
  simp only [hc,Nat.cast_zero,ciSup_const]

theorem zeroAlgorithm_cost {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
    (I : Instance G μ L ρ Δ R₀ σf σg) : I.cost (zeroAlgorithm G)=0 := by
  unfold Instance.cost seededCalls
  simp only [zeroAlgorithm_totalCalls,lintegral_zero]

theorem trivial_risk {G : Geometry} [Subsingleton G.X]
    {μ L ρ Δ R₀ σf σg : ℝ}
    (I : Instance G μ L ρ Δ R₀ σf σg) (A : Algorithm G) : I.risk A=0 := by
  unfold Instance.risk Instance.loss
  have hz (x : G.X) : gradient (I.primitive.hyperobjective I.response) x=0 :=
    Subsingleton.elim _ _
  simp only [hz,norm_zero,ENNReal.ofReal_zero,lintegral_zero]

def positiveClass {μ L ρ Δ R₀ σf σg : ℝ}
    (C : InstanceClass μ L ρ Δ R₀ σf σg) : InstanceClass μ L ρ Δ R₀ σf σg :=
  fun G I => C G I ∧ Nontrivial G.X

open Classical in
def extend (A : Solver) : Solver := fun G =>
  if Nontrivial G.X then A G else zeroAlgorithm G

theorem hardness_positive_dimensions {μ L ρ Δ R₀ σf σg ε rate : ℝ}
    {C : InstanceClass μ L ρ Δ R₀ σf σg}
    (hrate : 0<rate) (h : Hardness C ε rate) :
    Hardness (positiveClass C) ε rate := by
  classical
  intro A hA
  have hExt : Accurate C ε (extend A) := by
    intro G I hI
    by_cases hG : Nontrivial G.X
    · simpa only [extend,if_pos hG] using hA G I ⟨hI,hG⟩
    · letI : Subsingleton G.X := not_nontrivial_iff_subsingleton.mp hG
      rw [trivial_risk]
      exact zero_le _
  obtain ⟨G,I,hI,hcost⟩ := h (extend A) hExt
  have hG : Nontrivial G.X := by
    by_contra hG
    have hc : I.cost (extend A G)=0 := by
      rw [extend,if_neg hG,zeroAlgorithm_cost]
    rw [hc] at hcost
    have hp : 0<ENNReal.ofReal rate := ENNReal.ofReal_pos.mpr hrate
    exact (not_le_of_gt hp) hcost
  refine ⟨G,I,⟨hI,hG⟩,?_⟩
  simpa only [extend,if_pos hG] using hcost

theorem outer_dimension_positive (G : Geometry) :
    0<Module.finrank ℝ G.X ↔ Nontrivial G.X := Module.finrank_pos_iff

theorem inner_dimension_positive (G : Geometry) :
    0<Module.finrank ℝ G.Y := Module.finrank_pos

/-- The public finite dimensional Hilbert spaces have the exact Euclidean
coordinate representation used by the paper. -/
def outerCoordinates (G : Geometry) :
    G.X ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ G.X)) :=
  (stdOrthonormalBasis ℝ G.X).repr

def innerCoordinates (G : Geometry) :
    G.Y ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ G.Y)) :=
  (stdOrthonormalBasis ℝ G.Y).repr

end Bilevel.PolishedPositiveDimension
