import NCBall.TruncatedShadow
import NCBall.IndependentReplacement
import NCBall.HistoryMap

/-! # The complete random table of hidden directions and reusable sample noise -/

noncomputable section
open MeasureTheory
namespace NCBall

abbrev RoomLatents (n H M : ℕ) := Fin M → HandleLatent (Transverse n) H

def roomLatentLaw (n H M : ℕ) : Measure (RoomLatents n H M) :=
  Measure.pi (fun _ : Fin M => euclideanGaussianLaw (HandleLatent (Transverse n) H))

instance roomLatentLaw_probability (n H M : ℕ) : IsProbabilityMeasure (roomLatentLaw n H M) := by
  unfold roomLatentLaw
  infer_instance

def finiteRoomExtension {E : Type*} {n M : ℕ} (a : E → Space n) (w : Fin M → E) (k : ℕ) : Space n :=
  if hk : k < M then a (w ⟨k, hk⟩) else 0

theorem finiteRoomExtension_update {E : Type*} {n M : ℕ} (a : E → Space n)
    (w : Fin M → E) (j : Fin M) (z : E) :
    finiteRoomExtension a (Function.update w j z) =
      Function.update (finiteRoomExtension a w) j.val (a z) := by
  funext k
  by_cases hk : k = j.val
  · subst k
    simp [finiteRoomExtension, j.isLt]
  · rw [Function.update_of_ne hk]
    unfold finiteRoomExtension
    split_ifs with hkm
    · rw [Function.update_of_ne (show (⟨k, hkm⟩ : Fin M) ≠ j from fun he => hk (congrArg Fin.val he))]
    · rfl

theorem finiteRoomExtension_measurable {E : Type*} [MeasurableSpace E] {n M : ℕ}
    (a : E → Space n) (ha : Measurable a) (k : ℕ) :
    Measurable (fun w : Fin M → E => finiteRoomExtension a w k) := by
  unfold finiteRoomExtension
  split_ifs
  · exact ha.comp (measurable_pi_apply _)
  · exact measurable_const

def latentDirections {n H M : ℕ} (scale : ℝ) (w : RoomLatents n H M) : ℕ → Space n :=
  finiteRoomExtension (fun z => transverseEmbed n (scale • hiddenBlock (Transverse n) H z)) w

def latentSamples {n H M : ℕ} (σ scale : ℝ) (w : RoomLatents n H M) (h : Fin H) : ℕ → Space n :=
  finiteRoomExtension (fun z => transverseEmbed n (scale • z 0) +
    σ • transverseEmbed n (scale • z h.succ)) w

theorem latentDirections_clock {n H M : ℕ} (scale : ℝ) (w : RoomLatents n H M) (k : ℕ) :
    latentDirections scale w k 0 = 0 := by
  unfold latentDirections finiteRoomExtension
  split_ifs <;> simp [transverseEmbed_clock]

theorem latentDirections_measurable {n H M : ℕ} (scale : ℝ) (k : ℕ) :
    Measurable (fun w : RoomLatents n H M => latentDirections scale w k) := by
  apply finiteRoomExtension_measurable
  exact (transverseEmbed n).continuous.measurable.comp
    ((hiddenBlock (Transverse n) H).measurable.const_smul scale)

theorem latentSamples_measurable {n H M : ℕ} (σ scale : ℝ) (k : ℕ) :
    Measurable (fun wh : RoomLatents n H M × Fin H => latentSamples σ scale wh.1 wh.2 k) := by
  apply measurable_from_prod_countable
  intro h
  dsimp only [Prod.fst, Prod.snd, latentSamples]
  apply finiteRoomExtension_measurable
  have h0 : Measurable (fun z : HandleLatent (Transverse n) H => z 0) :=
    (hiddenBlock (Transverse n) H).measurable
  have hh : Measurable (fun z : HandleLatent (Transverse n) H => z h.succ) := by
    let e : HandleLatent (Transverse n) H →L[ℝ] Transverse n :=
      PiLp.proj 2 (fun _ : Fin (H + 1) => Transverse n) h.succ
    exact e.measurable
  exact ((transverseEmbed n).continuous.measurable.comp (h0.const_smul scale)).add
    (((transverseEmbed n).continuous.measurable.comp (hh.const_smul scale)).const_smul σ)

attribute [local irreducible] latentDirections latentSamples

def latentBackground {R : Type*} [MeasurableSpace R] (n H M : ℕ) (σ scale : ℝ) :
    RoomBackground (R × RoomLatents n H M) n H where
  directions s := latentDirections scale s.2
  samples s h := latentSamples σ scale s.2 h
  measurable_directions k := (latentDirections_measurable scale k).comp measurable_snd
  measurable_samples k := (latentSamples_measurable σ scale k).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem latentDirections_update {n H M : ℕ} (scale : ℝ) (w : RoomLatents n H M)
    (j : Fin M) (z : HandleLatent (Transverse n) H) :
    latentDirections scale (Function.update w j z) =
      Function.update (latentDirections scale w) j.val (transverseEmbed n (scale • z 0)) :=
  by
    unfold latentDirections
    exact finiteRoomExtension_update _ w j z

theorem latentSamples_update {n H M : ℕ} (σ scale : ℝ) (w : RoomLatents n H M)
    (j : Fin M) (z : HandleLatent (Transverse n) H) (h : Fin H) :
    latentSamples σ scale (Function.update w j z) h =
      Function.update (latentSamples σ scale w h) j.val
        (transverseEmbed n (scale • z 0) + σ • transverseEmbed n (scale • z h.succ)) :=
  by
    unfold latentSamples
    exact finiteRoomExtension_update _ w j z

end NCBall
