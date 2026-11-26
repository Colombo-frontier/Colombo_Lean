import Bilevel.ChiOuterExtensionTrace
import Bilevel.ChiCarrierSupportAlgebra

/-! Actual public radial fields preserve the disclosed lower subspace.
Their tangential gradient is a scalar times the query block at every normal
argument, so it remains public even though its norm is unbounded. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiCarrier ChiExtension PrimitiveGeometry PublicRadialExtension
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem radial_inner_contDiff (ν R dn t : ℝ) :
    ContDiff ℝ 3 (fun u : F => radial ν R dn (pack u t)) :=
  (potential_contDiff (ν*R/dn) R normalDirection 3).comp
    ((packLinear (X:=F) (Y:=ℝ)).contDiff.comp (contDiff_id.prodMk contDiff_const))

theorem radial_inner_gradient (ν R dn t : ℝ) (hR : 0<R) (u : F) :
    gradient (fun v : F => radial ν R dn (pack v t)) u=radialCoefficient ν R dn u t • u := by
  have hp := ((potential_contDiff (ν*R/dn) R (normalDirection : Joint F ℝ) 3).differentiable
    (by norm_num) (pack u t)).hasGradientAt
  change HasGradientAt (radial ν R dn) (pack
    ((gradient (radial ν R dn) (pack u t)).fst) ((gradient (radial ν R dn) (pack u t)).snd)) (pack u t) at hp
  have hx := (PrimitiveGeometry.partial_x hp).gradient
  exact hx.trans (radial_tangential_gradient ν R dn hR u t)

omit [CompleteSpace E] [CompleteSpace F] in
theorem hierarchyRadialTerm_inner_eq (m j s : ℕ) (i : Fin s) (ν R dn : ℝ)
    (a : E) (x : Blocks m F) (q : Normals s) :
    radialTerm s i (hierarchyBlock (E:=E) (F:=F) m j) (hierarchyBlock_norm_le (E:=E) (F:=F) m j) ν R dn (pack (pack a x) q)=
      radial ν R dn (pack (block m j x) (q i)) := rfl

omit [CompleteSpace E] in
theorem hierarchyRadialTerm_inner_support {m s : ℕ} (j : Fin m) (i : Fin s) (ν R dn : ℝ)
    (hR : 0<R) (a : E) (x : Blocks m F) (q : Normals s)
    (W : Fin m → Submodule ℝ F) (hx : x j∈W j) :
    gradient (fun y => radialTerm s i (hierarchyBlock (E:=E) (F:=F) m j.val)
      (hierarchyBlock_norm_le (E:=E) (F:=F) m j.val) ν R dn (pack (pack a y) q)) x∈knownSpace W := by
  change gradient ((fun u : F => radial ν R dn (pack u (q i))) ∘ block m j.val) x∈knownSpace W
  apply block_composition_gradient_mem W x j (radial_inner_contDiff ν R dn (q i))
  rw [radial_inner_gradient ν R dn (q i) hR]
  exact (W j).smul_mem _ hx

omit [CompleteSpace E] in
theorem hierarchyRadialSum_inner_support {m s J : ℕ} (hm : J < m)
    (index : Fin J → Fin s) (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (a : E) (x : Blocks m F) (q : Normals s) (W : Fin m → Submodule ℝ F)
    (hx : x∈knownSpace W) :
    gradient (fun y => radialSum index (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
      (fun i => hierarchyBlock_norm_le (E:=E) (F:=F) m (i.val+1)) (fun i => ρ (i.val+1)) (fun i => R (i.val+1)) dn
      (pack (pack a y) q)) x∈knownSpace W := by
  change gradient (fun y => ∑ i : Fin J,radial (ρ (i.val+1)) (R (i.val+1)) dn
    (pack (block m (i.val+1) y) (q (index i)))) x∈knownSpace W
  apply gradient_sum_mem Finset.univ (knownSpace W) _
    (fun i => (radial_inner_contDiff (ρ (i.val+1)) (R (i.val+1)) dn (q (index i))).comp
      (block (E:=F) m (i.val+1)).contDiff)
  intro i _
  exact hierarchyRadialTerm_inner_support ⟨i.val+1,by have := i.isLt;omega⟩ (index i)
    (ρ (i.val+1)) (R (i.val+1)) dn (hR i) a x q W (hx _)

end Bilevel.ChiOuter
