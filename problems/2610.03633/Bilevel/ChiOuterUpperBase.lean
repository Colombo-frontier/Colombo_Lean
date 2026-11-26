import Bilevel.ChiOuterReleaseCorrection
import Bilevel.ChiOuterWrappedRegularity

/-! The actual upper primitive base, separated from its macro-only term so
the lower-variable gradient never pays the macro chain length. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry RadialWrapper
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def baseRadial (m : ℕ) (ρ R : ℝ) (z : Joint E (Blocks m F)) : ℝ := bowl ρ R (block m 0 z.snd)

def baseLower (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (z : Joint E (Blocks m F)) : ℝ :=
  outerReleaseCorrection m M (fun i => D 0 [i.val]) z+outerCarrier m M D d 0 z+baseRadial m ρ R z

def upperBase (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (z : Joint E (Blocks m F)) : ℝ :=
  macroValue M.n M.ell M.width ν M.radius M.frame z.fst+baseLower m M D d ρ R z

omit [CompleteSpace E] [CompleteSpace F] in
theorem baseRadial_contDiff (m : ℕ) (ρ R : ℝ) : ContDiff ℝ 3 (baseRadial (E:=E) (F:=F) m ρ R) :=
  ((full_bowl_contDiff ρ R 3).comp (block (E:=F) m 0).contDiff).comp
    (innerProjection (E:=E) (F:=F) m).contDiff

theorem baseLower_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (ρ R : ℝ) :
    ContDiff ℝ 3 (baseLower m M D d ρ R) :=
  ((outerReleaseCorrection_contDiff m M (fun i => D 0 [i.val])).add (outerCarrier_contDiff m M D d 0)).add
    (baseRadial_contDiff m ρ R)

theorem upperBase_contDiff (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (d : ℕ) (ρ R : ℝ) :
    ContDiff ℝ 3 (upperBase m M ν D d ρ R) :=
  ((macro_contDiff M ν 3).comp (outerProjection (E:=E) (F:=F) m).contDiff).add (baseLower_contDiff m M D d ρ R)

omit [CompleteSpace E] [CompleteSpace F] in
theorem baseRadial_jet_le (m : ℕ) (ρ R : ℝ) (z : Joint E (Blocks m F)) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (baseRadial m ρ R) z‖≤‖iteratedFDeriv ℝ k (bowl ρ R) (block m 0 z.snd)‖ := by
  apply (contraction_jet_bound (innerProjection (E:=E) (F:=F) m) (innerProjection_norm_le m)
    ((full_bowl_contDiff ρ R 3).comp (block (E:=F) m 0).contDiff) z k hk).trans
  exact block_jet_contraction m 0 (full_bowl_contDiff ρ R 3) z.snd k hk

omit [CompleteSpace E] in
theorem baseRadial_first_bound (m : ℕ) (ρ R : ℝ) (hρ : 0≤ρ) (hR : 0<R) (z : Joint E (Blocks m F)) :
    ‖iteratedFDeriv ℝ 1 (baseRadial m ρ R) z‖≤ρ*R := by
  apply (baseRadial_jet_le m ρ R z 1 (by norm_num)).trans
  rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq,Regularity.bowl_gradient ρ R hR]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hρ]
  exact mul_le_mul_of_nonneg_left (compress_norm_le_radius R hR _) hρ

omit [CompleteSpace E] in
theorem baseRadial_second_bound (m : ℕ) (ρ R : ℝ) (hρ : 0≤ρ) (hR : 0<R) (z : Joint E (Blocks m F)) :
    ‖iteratedFDeriv ℝ 2 (baseRadial m ρ R) z‖≤ρ :=
  (baseRadial_jet_le m ρ R z 2 (by norm_num)).trans (Regularity.bowl_jet_two ρ R hρ hR _)

theorem baseLower_jet_bound (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (z : Joint E (Blocks m F)) (k : ℕ) (hk : k≤3) (Bc Br Bp : ℝ)
    (hc : ‖iteratedFDeriv ℝ k (outerReleaseCorrection m M (fun i => D 0 [i.val])) z‖≤Bc)
    (hr : ‖iteratedFDeriv ℝ k (outerCarrier m M D d 0) z‖≤Br)
    (hp : ‖iteratedFDeriv ℝ k (baseRadial m ρ R) z‖≤Bp) :
    ‖iteratedFDeriv ℝ k (baseLower m M D d ρ R) z‖≤Bc+Br+Bp := by
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  unfold baseLower
  rw [iteratedFDeriv_add_apply'
      ((((outerReleaseCorrection_contDiff m M (fun i => D 0 [i.val])).add (outerCarrier_contDiff m M D d 0)).of_le hk').contDiffAt)
      (((baseRadial_contDiff m ρ R).of_le hk').contDiffAt),
    iteratedFDeriv_add_apply' (((outerReleaseCorrection_contDiff m M (fun i => D 0 [i.val])).of_le hk').contDiffAt)
      (((outerCarrier_contDiff m M D d 0).of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hc hr)) hp)

theorem upperBase_second_bound (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (z : Joint E (Blocks m F)) (Bm Bl : ℝ)
    (hm : ‖iteratedFDeriv ℝ 2 (macroValue M.n M.ell M.width ν M.radius M.frame) z.fst‖≤Bm)
    (hl : ‖iteratedFDeriv ℝ 2 (baseLower m M D d ρ R) z‖≤Bl) :
    ‖iteratedFDeriv ℝ 2 (upperBase m M ν D d ρ R) z‖≤Bm+Bl := by
  have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
  change ‖iteratedFDeriv ℝ 2 (fun y => (macroValue M.n M.ell M.width ν M.radius M.frame ∘
    outerProjection (E:=E) (F:=F) m) y+baseLower m M D d ρ R y) z‖≤_
  rw [iteratedFDeriv_add_apply' ((((macro_contDiff M ν 3).comp
    (outerProjection (E:=E) (F:=F) m).contDiff).of_le h23).contDiffAt)
    (((baseLower_contDiff m M D d ρ R).of_le h23).contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add
    ((contraction_jet_bound (outerProjection (E:=E) (F:=F) m) (outerProjection_norm_le m)
      (macro_contDiff M ν 3) z 2 (by norm_num)).trans hm) hl)

theorem upperBase_lower_gradient_bound (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (d : ℕ) (ρ R : ℝ)
    (x : E) (v : Blocks m F) (B : ℝ)
    (hb : ‖iteratedFDeriv ℝ 1 (baseLower m M D d ρ R) (pack x v)‖≤B) :
    ‖gradient (fun w => upperBase m M ν D d ρ R (pack x w)) v‖≤B := by
  have hg := (((baseLower_contDiff m M D d ρ R).differentiable (by norm_num)) (pack x v)).hasGradientAt
  have hy := PrimitiveGeometry.partial_y hg
  rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq] at hb
  have he : (fun w => upperBase m M ν D d ρ R (pack x w))=
      fun w => macroValue M.n M.ell M.width ν M.radius M.frame x+baseLower m M D d ρ R (pack x w) := rfl
  rw [he,← norm_fderiv_eq_norm_gradient,fderiv_const_add,norm_fderiv_eq_norm_gradient,hy.gradient]
  exact (WithLp.norm_snd_le E (gradient (baseLower m M D d ρ R) (pack x v))).trans hb

end Bilevel.ChiOuter
