import GradientHessian.InnerCoordinates
import GradientHessian.InnerSelector
import GradientHessian.InverseGate
import GradientHessian.LatchLemma

/-! The literal inner objective, with one shared numerical coordinate and
disjoint Euclidean task registers. A task has `k + 2` registers, so its first
payload register is distinct from its last selector register. -/

noncomputable section
namespace GradientHessian.Inner

open scoped InnerProductSpace
open EuclideanRegisters InnerCoordinates

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radius (k : ℕ) : Fin (k + 2) → ℝ := LatchChain.sourceScale 1
def lastRadius (k : ℕ) : ℝ := 2 ^ (k + 1)
def payloadBound : ℝ := 19 * InverseGate.H₀ ^ 2 + 56

theorem radius_pos (k : ℕ) (j : Fin (k + 2)) : 0 < radius k j := by
  exact LatchChain.sourceScale_pos (by norm_num) j
@[simp] theorem radius_first (k : ℕ) : radius k 0 = 1 := by simp [radius, LatchChain.sourceScale]
@[simp] theorem radius_last (k : ℕ) : radius k (Fin.last (k + 1)) = lastRadius k := by
  simp [radius, lastRadius, LatchChain.sourceScale]
theorem payloadBound_pos : 0 < payloadBound := by
  dsimp [payloadBound]
  positivity

def block (v : Fin (k + 2) → E) (U : Registers E (k + 2)) : ℝ :=
  LatchChain.self (k + 1) v (radius k) 0 U
def input (v : Fin (k + 2) → E) (U : Registers E (k + 2)) : ℝ :=
  LatchChain.incoming 1 (v 0) (U 0)
def completion (v : Fin (k + 2) → E) (U : Registers E (k + 2)) : ℝ :=
  LatchChain.port (k + 1) v (radius k) U

def ports (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2)) (i : Fin m) : ℝ :=
  completion (v i) (tasks Y E m (k + 2) Z i)
def payload (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) : ℝ :=
  InverseGate.forcing (b i) (numerical Y E m (k + 2) Z) +
    input (v i) (tasks Y E m (k + 2) Z i) *
      InverseGate.gate (a i) (numerical Y E m (k + 2) Z)
def forcingSum (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) : ℝ := InnerSelector.select m (ports v Z) (payload b a v Z)
def selfSum (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2)) : ℝ :=
  ∑ i, block (v i) (tasks Y E m (k + 2) Z i)
def objective (A : Y →L[ℝ] Y) (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) : ℝ :=
  InverseGate.quadratic A (numerical Y E m (k + 2) Z) - forcingSum b a v Z + selfSum v Z
def outgoing (v : Fin (m + 1) → Fin (k + 2) → E) (Z : Space Y E (m + 1) (k + 2)) : ℝ :=
  ports v Z (Fin.last m)
def driven (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space Y E (m + 1) (k + 2)) : ℝ := objective A b a v Z - l * outgoing v Z

def publicQuadratic (m k : ℕ) (Z : Space Y E m (k + 2)) : ℝ :=
  ∑ i, LatchChain.publicQuadratic (k + 1) (radius k) (tasks Y E m (k + 2) Z i)
def residual (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) : ℝ := selfSum v Z - publicQuadratic m k Z - forcingSum b a v Z

theorem objective_decomposition (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2)) :
    objective A b a v Z = InverseGate.quadratic A (numerical Y E m (k + 2) Z) +
      publicQuadratic m k Z + residual b a v Z := by
  unfold objective residual
  ring

theorem forcingSum_eq_source (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) : forcingSum b a v Z =
      ∑ i, ((1 - ports v Z i) * ∏ j : Fin m, if j < i then ports v Z j else 1) * payload b a v Z i :=
  InnerSelector.select_eq_weighted_sum m _ _

theorem forcing_bounds (b y : Y) : InverseGate.forcing b y ∈ Set.Icc (0 : ℝ)
    (19 * InverseGate.H₀ ^ 2) := by
  have ht := IntegralProfiles.theta_abs_bound (InverseGate.forcingArg b y)
  have ht' := abs_le.mp ht
  have hs := sq_nonneg InverseGate.H₀
  unfold InverseGate.forcing
  constructor <;> nlinarith

theorem input_bounds (v : Fin (k + 2) → E) (U : Registers E (k + 2)) :
    input v U ∈ Set.Icc (0 : ℝ) 56 := by
  simpa [input] using LatchChain.incoming_bounds (by norm_num : (0 : ℝ) ≤ 1) (v 0) (U 0)
theorem completion_bounds (v : Fin (k + 2) → E) (U : Registers E (k + 2)) :
    completion v U ∈ Set.Icc (0 : ℝ) 1 := Profiles.varpi_bounds _
theorem ports_bounds (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2)) (i : Fin m) :
    ports v Z i ∈ Set.Icc (0 : ℝ) 1 := completion_bounds _ _
theorem payload_bounds (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) : payload b a v Z i ∈ Set.Icc (0 : ℝ) payloadBound := by
  have hB := input_bounds (v i) (tasks Y E m (k + 2) Z i)
  have hc := Profiles.chi_bounds (InverseGate.gateArg (a i) (numerical Y E m (k + 2) Z))
  have hf := forcing_bounds (b i) (numerical Y E m (k + 2) Z)
  change _ ∈ Set.Icc _ _ at hc
  have hmul := mul_le_mul_of_nonneg_left hc.2 hB.1
  have hmul0 := mul_nonneg hB.1 hc.1
  dsimp [payload, InverseGate.gate, payloadBound] at *
  constructor <;> nlinarith [hf.1, hf.2, hB.1, hB.2]
theorem forcingSum_bounds (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) : forcingSum b a v Z ∈ Set.Icc (0 : ℝ) payloadBound :=
  InnerSelector.select_bounds m _ _ payloadBound_pos.le (ports_bounds v Z) (payload_bounds b a v Z)

def taskProjection (m k : ℕ) (i : Fin m) : Space Y E m (k + 2) →L[ℝ] Registers E (k + 2) :=
  (PiLp.proj 2 _ i).comp (tasks Y E m (k + 2))

theorem block_contDiff (v : Fin (k + 2) → E) : ContDiff ℝ 3 (block v) :=
  LatchChain.self_contDiff _ _ _ _
theorem input_contDiff (v : Fin (k + 2) → E) : ContDiff ℝ 3 (input v) :=
  (LatchChain.incoming_contDiff 1 (v 0)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 2) => E) 0).contDiff
theorem completion_contDiff (v : Fin (k + 2) → E) : ContDiff ℝ 3 (completion v) :=
  LatchChain.port_contDiff _ _ _
theorem ports_contDiff (v : Fin m → Fin (k + 2) → E) (i : Fin m) :
    ContDiff ℝ 3 (fun Z : Space Y E m (k + 2) => ports v Z i) :=
  (completion_contDiff (v i)).comp (taskProjection (Y := Y) (E := E) m k i).contDiff
theorem payload_contDiff (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E) (i : Fin m) :
    ContDiff ℝ 3 (fun Z : Space Y E m (k + 2) => payload b a v Z i) := by
  have hU : ContDiff ℝ 3 (InverseGate.forcing (b i)) := by
    unfold InverseGate.forcing InverseGate.forcingArg
    exact contDiff_const.mul (contDiff_const.add
      ((IntegralProfiles.theta_contDiff.of_le (by decide : (3 : WithTop ℕ∞) ≤ 4)).comp
        ((innerSL ℝ (b i)).contDiff.div_const _)))
  exact (hU.comp (numerical Y E m (k + 2)).contDiff).add
    (((input_contDiff (v i)).comp (taskProjection (Y := Y) (E := E) m k i).contDiff).mul
      ((InverseGate.gate_contDiff (a i)).comp (numerical Y E m (k + 2)).contDiff))
theorem forcingSum_contDiff (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E) :
    ContDiff ℝ 3 (forcingSum b a v) :=
  InnerSelector.select_contDiff m _ _ (ports_contDiff v) (payload_contDiff b a v)
theorem selfSum_contDiff (v : Fin m → Fin (k + 2) → E) : ContDiff ℝ 3 (selfSum (Y := Y) v) := by
  exact ContDiff.sum (fun i _ => (block_contDiff (v i)).comp
    (taskProjection (Y := Y) (E := E) m k i).contDiff)
theorem objective_contDiff (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (k + 2) → E) : ContDiff ℝ 3 (objective A b a v) := by
  have hq : ContDiff ℝ 3 (InverseGate.quadratic A) :=
    contDiff_const.mul (contDiff_id.inner ℝ A.contDiff)
  exact ((hq.comp (numerical Y E m (k + 2)).contDiff).sub (forcingSum_contDiff b a v)).add
    (selfSum_contDiff v)
theorem driven_contDiff (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ) : ContDiff ℝ 3 (driven A b a v l) :=
  (objective_contDiff A b a v).sub (contDiff_const.mul (ports_contDiff v (Fin.last m)))

end GradientHessian.Inner
