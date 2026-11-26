import Geode.GeodesicCalculus
import Geode.LogMap

/-! Complete explicit geodesics with their verified ambient differential data. -/
namespace Geode.Lorentz

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure GeodesicLine where
  point : ℝ → Point E
  velocity : ℝ → Ambient E
  speedSq : ℝ
  position_deriv : ∀ t, HasDerivAt (fun s => (point s).val) (velocity t) t
  velocity_deriv : ∀ t, HasDerivAt velocity (speedSq • (point t).val) t
  tangent : ∀ t, form E (point t).val (velocity t) = 0
  norm_sq : ∀ t, form E (velocity t) (velocity t) = speedSq

variable {E}

noncomputable def GeodesicLine.constant (p : Point E) : GeodesicLine E where
  point := fun _ => p
  velocity := fun _ => 0
  speedSq := 0
  position_deriv := fun t => hasDerivAt_const t p.val
  velocity_deriv := fun t => by simpa using hasDerivAt_const t (0 : Ambient E)
  tangent := fun _ => by simp
  norm_sq := fun _ => by simp

noncomputable def GeodesicLine.ofUnit (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) (a : ℝ) : GeodesicLine E where
  point := fun t => unitGeodesic x u hu hn (a * t)
  velocity := rayVelocity x u a
  speedSq := a ^ 2
  position_deriv := hasDerivAt_rayVector x u a
  velocity_deriv := hasDerivAt_rayVelocity x u a
  tangent := rayVelocity_tangent x u hu hn a
  norm_sq := rayVelocity_norm_sq x u hu hn a

noncomputable def segmentLine (x y : Point E) : GeodesicLine E := by
  classical
  exact if h : x = y then GeodesicLine.constant x else
    GeodesicLine.ofUnit x (direction x y) (direction_tangent x y)
      (direction_unit x y h) (dist x y)

@[simp] theorem segmentLine_point (x y : Point E) (t : ℝ) :
    (segmentLine x y).point t = segment x y t := by
  classical
  unfold segmentLine segment
  split_ifs <;> simp only [GeodesicLine.constant, GeodesicLine.ofUnit, mul_comm]

@[simp] theorem segmentLine_velocity_zero (x y : Point E) :
    (segmentLine x y).velocity 0 = logMap x y := by
  classical
  by_cases h : x = y
  · subst y
    simp [segmentLine, GeodesicLine.constant]
  · simp [segmentLine, h, GeodesicLine.ofUnit, rayVelocity, logMap]

end Geode.Lorentz
