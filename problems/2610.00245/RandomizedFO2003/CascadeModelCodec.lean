import RandomizedFO2003.CascadeDecoderMeasurability
import RandomizedFO2003.ModelDecoder
import RandomizedFO2003.CensoredHistory

namespace RandomizedFO2003.Cascade

open Primitives MeasureTheory

variable {N n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def Data.coefficients (d : Data N E) : Coefficients N E := (d.A, d.a, d.b)

variable [CompleteSpace E]

theorem Data.coordinateFunction_gradient (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (x : Model.Space n) :
    gradient (d.coordinateFunction V) x = V (gradient d.energy (V.symm x)) := by
  have hg := RandomizedFO2003.Calculus.hasGradientAt_comp_linear
    V.symm.toContinuousLinearEquiv.toContinuousLinearMap (x := x)
    ((d.energy_contDiff 1).differentiable (by norm_num) (V.symm x)).hasGradientAt
  have hadj : V.symm.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      V.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℝ
    intro z
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner (𝕜 := ℝ) y (V.symm z) = inner (𝕜 := ℝ) (V y) z
    simpa only [V.apply_symm_apply] using (V.inner_map_map y (V.symm z)).symm
  rw [hadj] at hg
  exact hg.gradient

theorem Data.coordinateOracle_eq (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (x : Model.Space n) :
    Model.oracle (d.coordinateFunction V) x = ((d.blockOracle (V.symm x)).1, V (d.blockOracle (V.symm x)).2) :=
  Prod.ext rfl (d.coordinateFunction_gradient V x)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The concrete codec uses only public coefficients and the two permitted
physical answers, and returns the actual standard-coordinate oracle pair. -/
noncomputable def cascadeCodec (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n)
    (i : Fin (N + 1)) (h B α D C₀ K : ℝ) : Model.OracleCodec n E (Coefficients N E) where
  authorized := fun p => (coefficientsData N E p.1 B α D C₀ K).oracleAuthorized i (V.symm p.2)
  measurable_authorized := by
    letI : MeasurableSpace (BlockProduct (N + 1) E) := borel _
    letI : BorelSpace (BlockProduct (N + 1) E) := ⟨rfl⟩
    letI : BorelSpace (Coefficients N E) := Prod.borelSpace
    have hp : Measurable (fun p : Coefficients N E × Model.Space n => (p.1, V.symm p.2)) :=
      measurable_fst.prodMk (V.symm.continuous.measurable.comp measurable_snd)
    have hm := (coefficients_oracleAuthorized_measurable (N := N) (E := E) i B α D C₀ K).comp hp
    simpa only [Function.comp_def] using hm
  response := fun p =>
    let r := (coefficientsData N E p.1.1 B α D C₀ K).reconstruct i (h • p.2.1) p.2.2 (V.symm p.1.2)
    (r.1, V r.2)
  measurable_response := by
    letI : MeasurableSpace (BlockProduct (N + 1) E) := borel _
    letI : BorelSpace (BlockProduct (N + 1) E) := ⟨rfl⟩
    letI : BorelSpace (Coefficients N E) := Prod.borelSpace
    have hp : Measurable (fun p : (Coefficients N E × Model.Space n) × (E × E) =>
        (((p.1.1, h • p.2.1), p.2.2), V.symm p.1.2)) :=
      (((measurable_fst.fst.prodMk (measurable_const.smul measurable_snd.fst)).prodMk measurable_snd.snd).prodMk
        (V.symm.continuous.measurable.comp measurable_fst.snd))
    have hm := (coefficients_reconstruct_measurable (N := N) (E := E) i B α D C₀ K).comp hp
    have ho := hm.fst.prodMk (V.continuous.measurable.comp hm.snd)
    simpa only [Function.comp_def] using ho

/-- The response identity needed by `Model.Algorithm.decodedProgram` is
proved for the actual censored cascade, from self-adjointness and the
physical meanings of the marked and matrix answers. -/
theorem Data.cascadeCodec_correct (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (h : ℝ) (M U : E →L[ℝ] E) (u : E) (hA : IsSelfAdjoint (d.A i))
    (hforce : h • U u = d.b i) (hmatrix : ∀ y, U (M (U.adjoint y)) = d.A i y)
    (x : Model.Space n) :
    (cascadeCodec V i h d.B d.α d.D d.C₀ d.K).response (((d.publicData i).coefficients, x),
      (if (cascadeCodec V i h d.B d.α d.D d.C₀ d.K).authorized ((d.publicData i).coefficients, x) = true
        then U u else 0, U (M (U.adjoint (V.symm x i))))) =
      Model.oracle ((d.censorGate i).coordinateFunction V) x := by
  let z := V.symm x
  have hb : h • (if (d.publicData i).oracleAuthorized i z = true then U u else 0) =
      if (d.publicData i).oracleAuthorized i z = true then d.b i else 0 := by
    split_ifs <;> simp only [hforce, smul_zero]
  have hr : (d.publicData i).reconstruct i
      (h • (if (d.publicData i).oracleAuthorized i z = true then U u else 0))
      (U (M (U.adjoint (z i)))) z = (d.censorGate i).blockOracle z := by
    rw [hb, hmatrix]
    exact d.public_reconstruction i hA z
  rw [(d.censorGate i).coordinateOracle_eq V x]
  exact congrArg (fun r : ℝ × BlockProduct (N + 1) E => (r.1, V r.2)) hr

end RandomizedFO2003.Cascade
