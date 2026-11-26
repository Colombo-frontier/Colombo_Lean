import Bilevel.PartialLegendreBasic
import Bilevel.PrimitiveGeometry

/-! Jointly varying partial conjugates constructed from a small Lipschitz
full gradient. The optimizing point is the actual inverse from Basic. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem norm_pack_zero_left (y : Y) : ‖pack (0:X) y‖=‖y‖ := by
  simp [norm_pack]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem norm_pack_zero_right (x : X) : ‖pack x (0:Y)‖=‖x‖ := by
  simp [norm_pack]

omit [CompleteSpace X] [CompleteSpace Y] in
theorem norm_pack_le_add (x : X) (y : Y) : ‖pack x y‖≤‖x‖+‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sq]
  change ‖x‖^2+‖y‖^2≤(‖x‖+‖y‖)^2
  nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]

variable {δ : NNReal} {G : Joint X Y → Joint X Y} (hG : LipschitzWith δ G)

omit [CompleteSpace X] [CompleteSpace Y] in
include hG in
theorem jointSlice_lipschitz (x : X) :
    LipschitzWith δ (fun z : Y => (G (pack x z)).snd) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hh := hG.dist_le_mul (pack x z) (pack x w)
  rw [dist_eq_norm,dist_eq_norm] at hh ⊢
  have hnorm : ‖pack x z-pack x w‖=‖z-w‖ := by
    change ‖pack (x-x) (z-w)‖=‖z-w‖
    rw [sub_self,norm_pack_zero_left]
  rw [hnorm] at hh
  exact (WithLp.norm_snd_le X (G (pack x z)-G (pack x w))).trans hh

variable (hδ : δ<1)

def jointSolution (x : X) (y : Y) : Y := solution hδ (jointSlice_lipschitz hG x) y

omit [CompleteSpace X] in
theorem jointSolution_equation (x : X) (y : Y) :
    jointSolution hG hδ x y+(G (pack x (jointSolution hG hδ x y))).snd=y :=
  solution_equation hδ (jointSlice_lipschitz hG x) y

omit [CompleteSpace X] in
theorem jointSolution_of_equation (x : X) (y z : Y) (hz : z+(G (pack x z)).snd=y) :
    z=jointSolution hG hδ x y := solution_of_equation hδ (jointSlice_lipschitz hG x) y z hz

omit [CompleteSpace X] in
/-- Joint inverse continuity, including changes in the macro variable. -/
theorem jointSolution_lipschitz_bound (q r : Joint X Y) :
    ‖jointSolution hG hδ q.fst q.snd-jointSolution hG hδ r.fst r.snd‖ ≤
      ((1+(δ:ℝ))/(1-(δ:ℝ)))*‖q-r‖ := by
  let z := jointSolution hG hδ q.fst q.snd
  let w := jointSolution hG hδ r.fst r.snd
  have hz : z+(G (pack q.fst z)).snd=q.snd := jointSolution_equation hG hδ q.fst q.snd
  have hw : w+(G (pack r.fst w)).snd=r.snd := jointSolution_equation hG hδ r.fst r.snd
  have hid : z-w=(q.snd-r.snd)-((G (pack q.fst z)).snd-(G (pack r.fst w)).snd) := by
    rw [← hz,← hw]
    abel
  have ht := norm_sub_le (q.snd-r.snd) ((G (pack q.fst z)).snd-(G (pack r.fst w)).snd)
  rw [← hid] at ht
  have hg := hG.dist_le_mul (pack q.fst z) (pack r.fst w)
  rw [dist_eq_norm,dist_eq_norm] at hg
  have hpart := WithLp.norm_snd_le X (G (pack q.fst z)-G (pack r.fst w))
  have hpair : ‖pack q.fst z-pack r.fst w‖≤‖q.fst-r.fst‖+‖z-w‖ :=
    norm_pack_le_add (q.fst-r.fst) (z-w)
  have hbound := mul_le_mul_of_nonneg_left hpair δ.coe_nonneg
  have hqx := WithLp.norm_fst_le X (q-r)
  have hqy := WithLp.norm_snd_le X (q-r)
  have hδ0 : 0≤(δ:ℝ) := δ.coe_nonneg
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  change ‖z-w‖≤((1+(δ:ℝ))/(1-(δ:ℝ)))*‖q-r‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  change ‖q.fst-r.fst‖≤‖q-r‖ at hqx
  change ‖q.snd-r.snd‖≤‖q-r‖ at hqy
  change ‖(G (pack q.fst z)).snd-(G (pack r.fst w)).snd‖≤‖G (pack q.fst z)-G (pack r.fst w)‖ at hpart
  nlinarith

def jointConjugate (P : Joint X Y → ℝ) (q : Joint X Y) : ℝ :=
  conjugate hδ (jointSlice_lipschitz hG q.fst) (fun z => P (pack q.fst z)) q.snd

omit [CompleteSpace X] in
theorem jointConjugate_value (P : Joint X Y → ℝ) (q : Joint X Y) :
    jointConjugate hG hδ P q =
      ⟪q.snd,jointSolution hG hδ q.fst q.snd⟫-
        (‖jointSolution hG hδ q.fst q.snd‖^2/2+P (pack q.fst (jointSolution hG hδ q.fst q.snd))) := rfl

variable (P : Joint X Y → ℝ) (hP : ∀ q,HasGradientAt P (G q) q)
include hP

theorem jointSlice_hasGradientAt (x : X) (z : Y) :
    HasGradientAt (fun w => P (pack x w)) (G (pack x z)).snd z :=
  PrimitiveGeometry.partial_y (hP (pack x z))

theorem jointConjugate_maximizes (q : Joint X Y) (z : Y) :
    ⟪q.snd,z⟫-(‖z‖^2/2+P (pack q.fst z))≤jointConjugate hG hδ P q :=
  conjugate_maximizes hδ (jointSlice_lipschitz hG q.fst) _
    (jointSlice_hasGradientAt P hP q.fst) q.snd z

theorem jointConjugate_eq_supremum (q : Joint X Y) :
    jointConjugate hG hδ P q=
      sSup (Set.range (fun z => ⟪q.snd,z⟫-(‖z‖^2/2+P (pack q.fst z)))) :=
  conjugate_eq_supremum hδ (jointSlice_lipschitz hG q.fst) _
    (jointSlice_hasGradientAt P hP q.fst) q.snd

end Bilevel.PartialLegendre
