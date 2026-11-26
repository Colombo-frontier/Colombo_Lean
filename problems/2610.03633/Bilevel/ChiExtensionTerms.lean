import Bilevel.ChiExtensionSpace
import Bilevel.ChiCoarseGradient

/-! Actual coarse and radial terms on the common Euclidean space containing
all dual normals. The derivative estimates include every tangential and
normal variable. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiExtension
open PrimitiveGeometry SmallGapProfiles SmallGapLiftSupport

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def normalTerm (m : ℕ) (i : Fin m) (f : E → ℝ) (W : ℝ) : Full E m → ℝ :=
  ChiCoarse.extension f W ∘ normalSlice m i

theorem normalTerm_contDiff (m : ℕ) (i : Fin m) {f : E → ℝ}
    (hf : ContDiff ℝ 3 f) {W : ℝ} (hW : 0<W) : ContDiff ℝ 3 (normalTerm m i f W) :=
  (ChiCoarse.extension_contDiff hf hW).comp (normalSlice (E:=E) m i).contDiff

theorem normalTerm_formula (m : ℕ) (i : Fin m) (f : E → ℝ) (W : ℝ)
    (p : E) (q : Normals m) : normalTerm m i f W (pack p q)=f p*normal W (q i) := by
  simp only [normalTerm,Function.comp_apply,normalSlice_pack,ChiCoarse.extension,
    CompensatedMean.uProj_pack,CompensatedMean.sProj_pack]

theorem normalTerm_zero_trace (m : ℕ) (i : Fin m) (f : E → ℝ) {W : ℝ}
    (hW : 0<W) (p : E) : normalTerm m i f W (pack p 0)=0 := by
  rw [normalTerm_formula]
  change f p*normal W 0=0
  rw [normal_core W 0 hW (by rw [abs_zero];positivity),mul_zero]

set_option maxHeartbeats 1200000 in
theorem normalTerm_normal_gradient (m : ℕ) (i : Fin m) (f : E → ℝ) {W : ℝ}
    (hW : 0<W) (p : E) : HasGradientAt (fun q : Normals m => normalTerm m i f W (pack p q))
      (EuclideanSpace.single i (f p)) 0 := by
  have hd := ((normal_contDiff W hW).differentiable (by norm_num) 0).hasDerivAt
  rw [normal_deriv_core W 0 hW (by rw [abs_zero];positivity)] at hd
  let ev : Normals m →L[ℝ] ℝ := EuclideanSpace.proj i
  have hproj : HasFDerivAt ev ev (0:Normals m) := ev.hasFDerivAt
  have hd' : HasDerivAt (normal W) 1 (ev 0) := by simpa only [map_zero] using hd
  have hcomp := (hd'.comp_hasFDerivAt 0 hproj).const_mul (f p)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hcomp using 1
  · funext q
    exact normalTerm_formula m i f W p q
  · ext q
    simp [ev,InnerProductSpace.toDual_apply,EuclideanSpace.inner_single_left,mul_comm]

theorem normalTerm_coarse_jets (m : ℕ) (i : Fin m) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {N ℓ h M : ℝ} (hN : 1≤N) (hℓ : 0≤ℓ) (hh : 0<h) (hM : 0≤M)
    (hb : ∀ z,|f z|≤M*N*ℓ*h^2 ∧ ‖iteratedFDeriv ℝ 1 f z‖≤M*ℓ*h*Real.sqrt N ∧
      ‖iteratedFDeriv ℝ 2 f z‖≤M*ℓ ∧ ‖iteratedFDeriv ℝ 3 f z‖≤M*ℓ/h)
    (z : Full E m) :
    ‖iteratedFDeriv ℝ 1 (normalTerm m i f (h*N^(1/3:ℝ))) z‖≤2*C*M*N*ℓ*h^2 ∧
    ‖iteratedFDeriv ℝ 2 (normalTerm m i f (h*N^(1/3:ℝ))) z‖≤4*C*M*ℓ*h*(N^(1/3:ℝ))^2 ∧
    ‖iteratedFDeriv ℝ 3 (normalTerm m i f (h*N^(1/3:ℝ))) z‖≤8*C*M*ℓ*N^(1/3:ℝ) := by
  have hNp : 0<N := by linarith
  have hW : 0<h*N^(1/3:ℝ) := mul_pos hh (Real.rpow_pos_of_pos hNp _)
  have h2 := ChiCoarse.actual_coarse_extension_jets hf hN hℓ hh hM hb (normalSlice m i z)
  have hc (k : ℕ) (hk : k≤3) := contraction_jet (ChiCoarse.extension_contDiff hf hW)
    (normalSlice (E:=E) m i) (normalSlice_norm_le m i) z k hk
  exact ⟨(hc 1 (by norm_num)).trans (ChiCoarse.coarse_first_jet hf hN hℓ hh hM
    (fun x => ⟨(hb x).1,(hb x).2.1⟩) _),(hc 2 (by norm_num)).trans h2.1,
    (hc 3 (by norm_num)).trans h2.2⟩

variable [CompleteSpace F]

def radialTerm (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖≤1)
    (ν R d : ℝ) : Full E m → ℝ :=
  PublicRadialExtension.radial ν R d ∘ radialSlice m i L hL

omit [CompleteSpace F] in
theorem radialTerm_contDiff (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖≤1)
    (ν R d : ℝ) : ContDiff ℝ 3 (radialTerm m i L hL ν R d) :=
  (PublicRadialExtension.potential_contDiff _ _ _ 3).comp (radialSlice m i L hL).contDiff

omit [CompleteSpace F] in
theorem radialTerm_zero_trace (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖≤1)
    (ν R d : ℝ) (p : E) : radialTerm m i L hL ν R d (pack p 0)=0 := by
  exact PublicRadialExtension.radial_trace ν R d (L p)

theorem radialTerm_jets (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖≤1)
    (ν R d : ℝ) (hν : 0≤ν) (hR : 0<R) (hd : 0<d) (z : Full E m) :
    ‖iteratedFDeriv ℝ 2 (radialTerm m i L hL ν R d) z‖≤3*(ν*R/d) ∧
    ‖iteratedFDeriv ℝ 3 (radialTerm m i L hL ν R d) z‖≤9*ν/d := by
  have hb := PublicRadialExtension.radial_jet_bounds ν R d hν hR hd (radialSlice m i L hL z)
  have hc (k : ℕ) (hk : k≤3) := contraction_jet
    (PublicRadialExtension.potential_contDiff (ν*R/d) R PublicRadialExtension.normalDirection 3)
    (radialSlice m i L hL) (radialSlice_norm_le m i L hL) z k hk
  exact ⟨(hc 2 (by norm_num)).trans hb.1,(hc 3 (by norm_num)).trans hb.2⟩

end Bilevel.ChiExtension
