import SampleReuse.OracleAdaptiveBatch
import SecondOrder.VariableOracleProgram

/-! Literal adaptive batch programs: batch size and endpoints are functions
of the preceding numerical state, and every call reads its reserved block.
Their outputs are identified with the means used by adaptive confidence. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def adaptiveGradientChordProgram {S : Type} {H B d : ℕ} (hB : 0 < B)
    (reserved : Fin B → Fin H) (x y : S → Point d) (n : S → ℕ) (s : S) :=
  gradientBatchProgram (fun i => reserved (prefixHandles hB (n s) i)) (x s) (y s)

def adaptiveHessianChordProgram {S : Type} {H B d : ℕ} (hB : 0 < B)
    (reserved : Fin B → Fin H) (x y : S → Point d) (n : S → ℕ) (s : S) :=
  hessianBatchProgram (fun i => reserved (prefixHandles hB (n s) i)) (x s) (y s)

theorem adaptiveGradientChordProgram_exact_calls {S : Type} {H B d : ℕ} (hB : 0 < B)
    (reserved : Fin B → Fin H) (x y : S → Point d) (n : S → ℕ) (s : S) :
    OracleProgram.UsesExactly (2 * n s) (adaptiveGradientChordProgram hB reserved x y n s) :=
  gradientBatchProgram_exact_calls _ _ _

theorem adaptiveHessianChordProgram_exact_calls {S : Type} {H B d : ℕ} (hB : 0 < B)
    (reserved : Fin B → Fin H) (x y : S → Point d) (n : S → ℕ) (s : S) :
    OracleProgram.UsesExactly (2 * n s) (adaptiveHessianChordProgram hB reserved x y n s) :=
  hessianBatchProgram_exact_calls _ _ _

theorem adaptiveGradientChordProgram_measurable {S : Type} [MeasurableSpace S]
    {H B d : ℕ} (hB : 0 < B) (q₀ : PersistentQuery H d) (reserved : Fin B → Fin H)
    (x y : S → Point d) (hx : Measurable x) (hy : Measurable y)
    (n : S → ℕ) (hn : Measurable n) :
    OracleProgram.MeasurableFamily q₀ 0 (adaptiveGradientChordProgram hB reserved x y n) := by
  apply OracleProgram.MeasurableFamily.chooseNat
    (fun k s => gradientBatchProgram (fun i => reserved (prefixHandles hB k i)) (x s) (y s))
    _ n hn
  intro k
  exact (gradientBatchProgram_measurableFamily q₀).comp
    (fun s => ((fun i => reserved (prefixHandles hB k i)), x s, y s))
    (measurable_const.prodMk (hx.prodMk hy))

theorem adaptiveHessianChordProgram_measurable {S : Type} [MeasurableSpace S]
    {H B d : ℕ} (hB : 0 < B) (q₀ : PersistentQuery H d) (reserved : Fin B → Fin H)
    (x y : S → Point d) (hx : Measurable x) (hy : Measurable y)
    (n : S → ℕ) (hn : Measurable n) :
    OracleProgram.MeasurableFamily q₀ 0 (adaptiveHessianChordProgram hB reserved x y n) := by
  apply OracleProgram.MeasurableFamily.chooseNat
    (fun k s => hessianBatchProgram (fun i => reserved (prefixHandles hB k i)) (x s) (y s))
    _ n hn
  intro k
  exact (hessianBatchProgram_measurableFamily q₀).comp
    (fun s => ((fun i => reserved (prefixHandles hB k i)), x s, y s))
    (measurable_const.prodMk (hx.prodMk hy))

theorem adaptiveGradientChordProgram_output {Ω S : Type} {H B d : ℕ} (hB : 0 < B)
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (reserved : Fin B → Fin H)
    (x y : S → Point d) (n : S → ℕ) (s : S) (tape : SampleTape H Ω) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (adaptiveGradientChordProgram hB reserved x y n s)
    alg.output (2 * n s) (persistentRun alg.toQueryPolicy F tape (2 * n s)) =
      adaptiveBatchMean hB (fun s => gradientChordSample F (x s, y s)) n s
        (fun i => tape (reserved i)) :=
  gradientBatchProgram_compiled_output q₀ F tape _ _ _

theorem adaptiveHessianChordProgram_output {Ω S : Type} {H B d : ℕ} (hB : 0 < B)
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (reserved : Fin B → Fin H)
    (x y : S → Point d) (n : S → ℕ) (s : S) (tape : SampleTape H Ω) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (adaptiveHessianChordProgram hB reserved x y n s)
    alg.output (2 * n s) (persistentRun alg.toQueryPolicy F tape (2 * n s)) =
      adaptiveBatchMean hB (fun s => hessianChordSample F (x s, y s)) n s
        (fun i => tape (reserved i)) :=
  hessianBatchProgram_compiled_output q₀ F tape _ _ _

end
end SampleReuse
