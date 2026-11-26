import Smoothness2601.Population
import Bilevel.HistoryOracle
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Concrete finite-budget adaptive execution. Each step chooses f or g and
receives one full gradient. Internal memory is arbitrary; the oracle maintains
arbitrary hidden history and is valid at every query/history. The execution
uses actual probability kernels, and expected norm uses a nonnegative integral
so a divergent integral cannot accidentally certify success. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry
open scoped ENNReal
namespace Smoothness2601.Adaptive

variable (X Y : Type*)
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

instance jointMeasurableSpace : MeasurableSpace (Joint X Y) := borel (Joint X Y)
instance jointBorelSpace : BorelSpace (Joint X Y) := ⟨rfl⟩

abbrev Query := Bool × (X × Y)

variable {X Y}

def trueGradient {b : Budgets} (P : Population (X := X) (Y := Y) b)
    (q : Query X Y) : Joint X Y :=
  if q.1 then P.grad_g (pack q.2.1 q.2.2) else P.grad_f (pack q.2.1 q.2.2)

/-- One full gradient costs one sample. The second output is private oracle
history, inaccessible to the algorithm except through the observed gradient. -/
structure Oracle {b : Budgets} (P : Population (X := X) (Y := Y) b)
    (History : Type) [MeasurableSpace History] where
  law : Kernel (Query X Y × History) (Joint X Y × History)
  markov : IsMarkovKernel law
  square_integrable : ∀ q h,
    Integrable (fun z => ‖z.1 - trueGradient P q‖^2) (law (q,h))
  centered : ∀ q h, (∫ z, z.1 - trueGradient P q ∂law (q,h)) = 0
  variance : ∀ q h, (∫ z, ‖z.1 - trueGradient P q‖^2 ∂law (q,h)) ≤ b.σ^2

attribute [instance] Oracle.markov

/-- All private random choices can be retained in Memory. The algorithm may
query anywhere and output any measurable point, with no span constraint. -/
structure Algorithm (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace (Joint X Y)] where
  Memory : Type
  [memoryMeasurable : MeasurableSpace Memory]
  initialLaw : Kernel (X × Y) Memory
  initialMarkov : IsMarkovKernel initialLaw
  query : ℕ → Memory → Query X Y
  query_measurable : ∀ k, Measurable (query k)
  update : ℕ → Memory × Joint X Y → Memory
  update_measurable : ∀ k, Measurable (update k)
  output : Memory → X
  output_measurable : Measurable output

attribute [instance] Algorithm.memoryMeasurable Algorithm.initialMarkov

variable {b : Budgets} {P : Population (X := X) (Y := Y) b}
    {H : Type} [MeasurableSpace H]
    (A : Algorithm X Y) (O : Oracle P H)

def inputAt (k : ℕ) (s : A.Memory × H) : Query X Y × H := (A.query k s.1, s.2)

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem inputAt_measurable (k : ℕ) : Measurable (inputAt A (H := H) k) :=
  ((A.query_measurable k).comp measurable_fst).prodMk measurable_snd

def finishAt (k : ℕ) (z : (A.Memory × H) × (Joint X Y × H)) : A.Memory × H :=
  (A.update k (z.1.1, z.2.1), z.2.2)

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [BorelSpace X] [SecondCountableTopology X] [BorelSpace Y] [SecondCountableTopology Y] in
theorem finishAt_measurable (k : ℕ) : Measurable (finishAt A (H := H) k) := by
  exact ((A.update_measurable k).comp
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_snd)

def step (k : ℕ) : Kernel (A.Memory × H) (A.Memory × H) :=
  Bilevel.Stateful.KernelMap.dependent
    (O.law.comap (inputAt A k) (inputAt_measurable A k)) (finishAt A k)

instance step_markov (k : ℕ) : IsMarkovKernel (step A O k) :=
  Bilevel.Stateful.KernelMap.dependent_markov _ _ (finishAt_measurable A k)

/-- Exactly N one-sample calls, with no expectation-based stopping criterion. -/
def execution : ℕ → Kernel (A.Memory × H) (A.Memory × H)
  | 0 => Kernel.id
  | n+1 => step A O n ∘ₖ execution n

instance execution_markov (n : ℕ) : IsMarkovKernel (execution A O n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (step A O n ∘ₖ execution A O n)
    infer_instance

def initialState (h : H) : Kernel (X × Y) (A.Memory × H) :=
  A.initialLaw.map (fun m => (m,h))

instance initialState_markov (h : H) : IsMarkovKernel (initialState A h) :=
  Kernel.IsMarkovKernel.map _ (measurable_id.prodMk measurable_const)

def outputKernel (n : ℕ) (h : H) : Kernel (X × Y) X :=
  (execution A O n ∘ₖ initialState A h).map (fun s => A.output s.1)

instance outputKernel_markov (n : ℕ) (h : H) : IsMarkovKernel (outputKernel A O n h) :=
  Kernel.IsMarkovKernel.map _ (A.output_measurable.comp measurable_fst)

variable [FiniteDimensional ℝ Y]

def expectedNorm (n : ℕ) (h : H) (x₀ : X) (y₀ : Y) : ℝ≥0∞ :=
  ∫⁻ x, (‖gradient P.objective x‖₊ : ℝ≥0∞) ∂outputKernel A O n h (x₀,y₀)

def Succeeds (n : ℕ) (ε : ℝ) (h : H) (x₀ : X) (y₀ : Y) : Prop :=
  expectedNorm A O n h x₀ y₀ ≤ ENNReal.ofReal ε

end Smoothness2601.Adaptive
