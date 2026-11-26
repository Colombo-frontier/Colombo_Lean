import NCConcave16991.AcceleratedSteps
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! # Canonical product sigma-algebras for the actual accelerated state and result -/

namespace NCConcave16991.Accelerated

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]

instance stateMeasurableSpace : MeasurableSpace (State X Y) :=
  MeasurableSpace.comap (fun s ↦ (s.y, s.z, s.primalSum)) inferInstance

instance proxResultMeasurableSpace : MeasurableSpace (ProxResult (X := X) (Y := Y)) :=
  MeasurableSpace.comap (fun r ↦ (r.x, r.y, r.normalX, r.normalY)) inferInstance

theorem state_coordinates_measurable : Measurable (fun s : State X Y ↦ (s.y, s.z, s.primalSum)) :=
  measurable_iff_comap_le.mpr le_rfl

theorem proxResult_coordinates_measurable :
    Measurable (fun r : ProxResult (X := X) (Y := Y) ↦ (r.x, r.y, r.normalX, r.normalY)) :=
  measurable_iff_comap_le.mpr le_rfl

@[fun_prop] theorem state_y_measurable : Measurable (State.y (X := X) (Y := Y)) :=
  measurable_fst.comp state_coordinates_measurable

@[fun_prop] theorem state_z_measurable : Measurable (State.z (X := X) (Y := Y)) :=
  measurable_fst.comp (measurable_snd.comp state_coordinates_measurable)

@[fun_prop] theorem state_primalSum_measurable : Measurable (State.primalSum (X := X) (Y := Y)) :=
  measurable_snd.comp (measurable_snd.comp state_coordinates_measurable)

@[fun_prop] theorem proxResult_x_measurable : Measurable (ProxResult.x (X := X) (Y := Y)) :=
  measurable_fst.comp proxResult_coordinates_measurable

@[fun_prop] theorem proxResult_y_measurable : Measurable (ProxResult.y (X := X) (Y := Y)) :=
  measurable_fst.comp (measurable_snd.comp proxResult_coordinates_measurable)

@[fun_prop] theorem proxResult_normalX_measurable : Measurable (ProxResult.normalX (X := X) (Y := Y)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp proxResult_coordinates_measurable))

@[fun_prop] theorem proxResult_normalY_measurable : Measurable (ProxResult.normalY (X := X) (Y := Y)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp proxResult_coordinates_measurable))

@[fun_prop] theorem state_mk_measurable :
    Measurable (fun a : Y × Y × X ↦ (⟨a.1, a.2.1, a.2.2⟩ : State X Y)) := by
  rw [measurable_comap_iff]
  exact measurable_id

@[fun_prop] theorem proxResult_mk_measurable :
    Measurable (fun a : X × Y × X × Y ↦ (⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩ : ProxResult (X := X) (Y := Y))) := by
  rw [measurable_comap_iff]
  exact measurable_id

end NCConcave16991.Accelerated
