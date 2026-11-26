import Bilevel.ChiSourceGoodEvent
import Bilevel.ChiSourceActivation
import Bilevel.ChiPrefixFrame

/-! The actual capped output receives its own terminal observation. On the
same source event, nonactivation of the finite hierarchy leaves the last
macro coordinate blind, even when the returned point was never queried. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution BorelAdaptive EuclideanGaussian

variable {C S Q O Y : Type*} [MeasurableSpace C] [MeasurableSpace S]
  [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]

def macroTerminal {counts : ℕ → ℕ} {J D : ℕ} (R : ℝ) (point : Y → Space D) :
    FrameIndex counts J → Y → Space D := fun _ y => RadialWrapper.compress R (point y)

theorem macroTerminal_measurable {counts : ℕ → ℕ} {J D : ℕ}
    (R : ℝ) (point : Y → Space D) (hp : Measurable point) (i : FrameIndex counts J) :
    Measurable (macroTerminal R point i) :=
  (RadialWrapper.compress_contDiff R 0).continuous.measurable.comp hp

omit [MeasurableSpace C] in
theorem sourceGood_macro_last {counts : ℕ → ℕ} {J D m : ℕ}
    (hD : ∀ i : FrameIndex counts J,chainSize i+1≤D) (A : Program S Q O Y)
    (evaluate : Q → Store counts J (Space D) → Store counts J (Space D) → Bool → O)
    (he : Measurable (fun p : Q × (Store counts J (Space D) × (Store counts J (Space D) × Bool)) =>
      evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (queries : Fin m → Q × Store counts J (Space D) → Space D) (hq : ∀ l,Measurable (queries l))
    (R width cap : ℝ) (hR : 0<R) (hw : 0<width) (hcap : 0≤cap)
    (hsmall : R*Real.sqrt cap≤width/8)
    (point : Y → Space D) (hp : Measurable point) (initial : C → S) (draws : C → ℕ → Bool)
    (N : ℕ) (p : C × Orientations counts J D)
    (hgood : sourceGood counts J D m hD A evaluate he queries hq (macroTerminal R point)
      (macroTerminal_measurable R point hp) initial draws N cap p)
    (hcount : (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).2.1<
      ChiTreeProgress.capacity counts (J+1) 0) :
    WrappedChain.coordinates (counts 0) R (frame hD p.2 (Sum.inl ()))
      (point (A.output (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).1))
        (Fin.last (counts 0))<width := by
  have hk := macro_incomplete_of_successes_lt counts J _ hcount
  have h := sourceGood_terminal counts J D m hD A evaluate he queries hq (macroTerminal R point)
    (macroTerminal_measurable R point hp) initial draws N cap hcap p hgood
    (Sum.inl ()) (Fin.last (counts 0)) hk
  dsimp only [macroTerminal] at h
  have hc : WrappedChain.coordinates (counts 0) R (frame hD p.2 (Sum.inl ()))
      (point (A.output (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).1))
      (Fin.last (counts 0))=
      ⟪columns hD p.2 (Sum.inl ()) (Fin.last (counts 0)),RadialWrapper.compress R
        (point (A.output (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).1))⟫ :=
    (ChiPrefixEvaluation.coordinates_inner _ R _ _ _).trans
      (congrArg (fun w => ⟪w,RadialWrapper.compress R
        (point (A.output (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).1))⟫)
        (frame_basis hD p.2 (Sum.inl ()) (Fin.last (counts 0))))
  rw [hc]
  apply lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt h ?_)
  have hn := RadialWrapper.compress_norm_le_radius R hR
    (point (A.output (run counts J A evaluate (columns hD p.2) (initial p.1) (draws p.1) N).1))
  have hm := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg cap)
  have hh : Real.sqrt cap*R≤width/8 := by simpa only [mul_comm] using hsmall
  exact (hm.trans hh).trans_lt (by linarith)

end Bilevel.ChiHierarchyHaar
