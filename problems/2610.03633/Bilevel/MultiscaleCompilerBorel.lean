import Bilevel.MultiscaleFrameCompiler
import Bilevel.MultiscaleOriginalFrameBorel

/-! Joint Borel identities for the literal finite-store compiler and its
actual Haar-indexed original response/loss. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000
open MeasureTheory
namespace Bilevel.MultiscaleMean
open SingleFrameSource ChiHierarchyIndex ChiHierarchyHaar CompensatedMean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)] {n : ℕ}

theorem innerEvaluate_measurable (P : Parameters (E:=E) n) (p : ℝ) :
    Measurable (fun z : InnerQuery E × (SingleFrameSource.Store n E × (SingleFrameSource.Store n E × Bool)) =>
      innerEvaluate P p z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let T := InnerQuery E × (SingleFrameSource.Store n E × (SingleFrameSource.Store n E × Bool))
  have ho : Measurable (fun z : T => z.2.1) := measurable_fst.comp measurable_snd
  have hn : Measurable (fun z : T => z.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hb : Measurable (fun z : T => z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hargs : Measurable (fun z : T =>
      (((macroColumns n z.2.1,macroColumns n z.2.2.1),z.1),((z.2.1.1,z.2.2.1.1),z.2.2.2))) :=
    ((((macroColumns_measurable n).comp ho).prodMk ((macroColumns_measurable n).comp hn)).prodMk measurable_fst).prodMk
      (((measurable_fst.comp ho).prodMk (measurable_fst.comp hn)).prodMk hb)
  have h := (P.disclosedReply_measurable p).comp hargs
  exact h

variable {D : ℕ}

theorem innerFrame_columns_measurable (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D) :
    Measurable (fun a : Orientations (counts n) 0 D => fun k : Fin (n+1) =>
      frame hD a (Sum.inl ()) (ZeroChain.basis k)) := by
  have he : (fun a : Orientations (counts n) 0 D => fun k : Fin (n+1) =>
      frame hD a (Sum.inl ()) (ZeroChain.basis k))=(fun a => columns hD a (Sum.inl ())) := by
    funext a k
    exact frame_basis hD a (Sum.inl ()) k
  rw [he]
  exact (measurable_pi_apply (Sum.inl ())).comp (columns_measurable hD)

theorem innerFrameReply_measurable
    [MeasurableSpace (LowerSpace (EuclideanGaussian.Space D))]
    [BorelSpace (LowerSpace (EuclideanGaussian.Space D))]
    (P : Parameters (E:=EuclideanGaussian.Space D) n) (p : ℝ)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D) :
    Measurable (fun z : Orientations (counts n) 0 D × (InnerQuery (EuclideanGaussian.Space D) × Bool) =>
      innerFrameReply P p hD z.1 z.2.1 z.2.2) :=
  innerOriginalReply_frame_measurable P (fun a => frame hD a (Sum.inl ())) (innerFrame_columns_measurable hD) p

theorem innerFrameLoss_measurable
    [MeasurableSpace (LowerSpace (EuclideanGaussian.Space D))]
    [BorelSpace (LowerSpace (EuclideanGaussian.Space D))]
    (P : Parameters (E:=EuclideanGaussian.Space D) n)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D) :
    Measurable (Function.uncurry (innerFrameLoss P hD)) :=
  innerOriginalLoss_frame_measurable P (fun a => frame hD a (Sum.inl ())) (innerFrame_columns_measurable hD)

end Bilevel.MultiscaleMean
