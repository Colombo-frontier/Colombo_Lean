import HeavyTail.ProximalOracle
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
The manuscript's information model. PublicProblem contains only known geometry,
regularization and parameters. PrivateInstance contains the unknown objective
and query-dependent oracle. The effective domain S may be smaller than X; in
particular the supplied initial point need not belong to S. Objective error is
ENNReal-valued and is infinite for feasible outputs outside S.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace Classical
namespace HeavyTail

structure OracleParameters where
  p : ℝ
  G : ℝ
  D : ℝ
  L : ℝ
  s : ℝ
  μ : ℝ
  δ : ℝ
  T : ℕ
  p_gt_one : 1 < p
  p_le_two : p ≤ 2
  G_pos : 0 < G
  D_pos : 0 < D
  s_pos : 0 < s
  s_le_L : s ≤ L
  μ_nonneg : 0 ≤ μ
  δ_pos : 0 < δ
  δ_lt_tenth : δ < 1 / 10

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

structure PublicProblem (θ : OracleParameters) where
  X : Set E
  X_nonempty : X.Nonempty
  X_closed : IsClosed X
  X_convex : Convex ℝ X
  S : Set E
  domain_nonempty : S.Nonempty
  domain_subset : S ⊆ X
  h : E → ℝ
  epigraph_closed : IsClosed {z : E × ℝ | z.1 ∈ S ∧ h z.1 ≤ z.2}
  h_convex : ConvexOn ℝ S h
  h_strongConvex : StrongConvexOn S θ.μ h
  prox : ProximalOracle S h
  initial : E
  initial_feasible : initial ∈ X

variable {E} {θ : OracleParameters}

namespace PublicProblem

theorem sublevel_closed (B : PublicProblem E θ) (t : ℝ) :
    IsClosed {x | x ∈ B.S ∧ B.h x ≤ t} :=
  B.epigraph_closed.preimage (continuous_id.prodMk continuous_const)

theorem domain_measurable (B : PublicProblem E θ) : MeasurableSet B.S := by
  have he : B.S = ⋃ n : ℕ, {x | x ∈ B.S ∧ B.h x ≤ n} := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (B.h x)
      exact ⟨n, hx, hn⟩
    · rintro ⟨_, hx, _⟩
      exact hx
  rw [he]
  exact MeasurableSet.iUnion fun n => (B.sublevel_closed n).measurableSet

theorem regularizer_measurable (B : PublicProblem E θ) :
    Measurable (fun x : B.S => B.h x) := by
  apply measurable_of_Iic
  intro t
  have hc := (B.sublevel_closed t).preimage
    (continuous_subtype_val : Continuous (Subtype.val : B.S → E))
  have he : ((fun x : B.S => B.h x) ⁻¹' Iic t) =
      Subtype.val ⁻¹' {x | x ∈ B.S ∧ B.h x ≤ t} := by
    ext x
    simp [x.property]
  rw [he]
  exact hc.measurableSet

end PublicProblem

structure PrivateInstance (B : PublicProblem E θ) where
  f : E → ℝ
  f_convex : ConvexOn ℝ B.X f
  f_lipschitz : LipschitzOnWith ⟨θ.G, θ.G_pos.le⟩ f B.X
  oracle : Kernel B.X E
  oracle_probability : IsMarkovKernel oracle
  reply_integrable : ∀ x, Integrable (fun g : E => g) (oracle x)
  mean_subgradient : ∀ x : B.X, ∀ y ∈ B.X,
    f x + ⟪∫ g, g ∂oracle x, y - x⟫_ℝ ≤ f y
  noise_memLp : ∀ x : B.X,
    MemLp (fun g => g - ∫ z, z ∂oracle x) (ENNReal.ofReal θ.p) (oracle x)
  strong_moment : ∀ x : B.X,
    (∫ g, ‖g - ∫ z, z ∂oracle x‖ ^ θ.p ∂oracle x) ≤ θ.L ^ θ.p
  weak_moment : ∀ x : B.X, ∀ v : E, ‖v‖ = 1 →
    (∫ g, |⟪v, g - ∫ z, z ∂oracle x⟫_ℝ| ^ θ.p ∂oracle x) ≤ θ.s ^ θ.p
  minimizer : E
  minimizer_domain : minimizer ∈ B.S
  minimizing : ∀ y ∈ B.S, f minimizer + B.h minimizer ≤ f y + B.h y
  initial_distance : ‖B.initial - minimizer‖ ≤ θ.D

namespace PrivateInstance
variable {B : PublicProblem E θ}

instance oracle_markov (I : PrivateInstance B) : IsMarkovKernel I.oracle :=
  I.oracle_probability

def mean (I : PrivateInstance B) (x : B.X) : E := ∫ g, g ∂I.oracle x

def optimalValue (I : PrivateInstance B) : ℝ := I.f I.minimizer + B.h I.minimizer

def loss (I : PrivateInstance B) (x : B.X) : ℝ≥0∞ :=
  if (x : E) ∈ B.S then ENNReal.ofReal (I.f x + B.h x - I.optimalValue) else ⊤

theorem gap_nonneg (I : PrivateInstance B) {x : E} (hx : x ∈ B.S) :
    0 ≤ I.f x + B.h x - I.optimalValue := sub_nonneg.mpr (I.minimizing x hx)

theorem loss_of_mem (I : PrivateInstance B) (x : B.X) (hx : (x : E) ∈ B.S) :
    I.loss x = ENNReal.ofReal (I.f x + B.h x - I.optimalValue) := by simp [loss, hx]

theorem loss_of_not_mem (I : PrivateInstance B) (x : B.X) (hx : (x : E) ∉ B.S) :
    I.loss x = ⊤ := by simp [loss, hx]

theorem loss_lt_top_iff (I : PrivateInstance B) (x : B.X) :
    I.loss x < ⊤ ↔ (x : E) ∈ B.S := by
  by_cases hx : (x : E) ∈ B.S <;> simp [loss, hx]

theorem loss_at_minimizer (I : PrivateInstance B) :
    I.loss ⟨I.minimizer, B.domain_subset I.minimizer_domain⟩ = 0 := by
  simp [loss, I.minimizer_domain, optimalValue]

theorem f_measurable (I : PrivateInstance B) : Measurable (fun x : B.X => I.f x) :=
  I.f_lipschitz.to_restrict.continuous.measurable

theorem loss_measurable (I : PrivateInstance B) : Measurable I.loss := by
  let S' : Set B.X := Subtype.val ⁻¹' B.S
  have hS' : MeasurableSet S' := B.domain_measurable.preimage measurable_subtype_coe
  have hh : Measurable (fun x : S' => B.h (x : B.X)) := by
    exact B.regularizer_measurable.comp
      ((measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk :
        Measurable (fun x : S' => (⟨((x : B.X) : E), x.property⟩ : B.S)))
  have hv : Measurable (fun x : S' => ENNReal.ofReal
      (I.f (x : B.X) + B.h (x : B.X) - I.optimalValue)) :=
    (((I.f_measurable.comp measurable_subtype_coe).add hh).sub_const _).ennreal_ofReal
  exact hv.dite (measurable_const (a := (⊤ : ℝ≥0∞))) hS'

end PrivateInstance
end HeavyTail
