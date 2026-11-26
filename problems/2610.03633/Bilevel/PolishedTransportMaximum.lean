import Bilevel.TransportRoundFrameEnergy
import Bilevel.TransportObserverQueryInsertion
import Bilevel.PolishedObserverMaximum

/-! The manuscript's distinct local/global maximum ledger. The local
energy set is the fixed complement of the edge-protected set; the global
energy set may be smaller. The edge estimate is applied to the actual
frame, paired history and orthogonal map. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
namespace Bilevel.PolishedTransportMaximum
open EuclideanGaussian ProjectionGeometry TransportObserver TransportEdgePosterior OrthogonalAction TransportNetwork TransportRound

theorem good_angle_smaller_destination {D : ℕ}
    (Wlocal Wglobal R : Submodule ℝ (Space D)) (O : OrthogonalHaar.Group D)
    (hW : Wlocal≤Wglobal) (hg : ¬TransportControllerEdge.angleBad Wglobal R O) :
    ¬TransportControllerEdge.angleBad Wlocal R O := by
  rintro ⟨u,hu⟩
  exact hg ⟨u,hu.trans_le (project_norm_mono hW _)⟩

/-- One actual forward or reverse action controls both destinations and
derives the paired-domain inclusions used by the next action. The same
theorem applies to O inverse, with the freshly enlarged local source. -/
theorem actual_directed_local_global {D T : ℕ}
    (V : Fin T → Space D) (hV : Orthonormal ℝ V)
    (O : OrthogonalHaar.Group D) (P : Pairs D) (hP : Supports P O)
    (S F Wlocal Wglobal : Submodule ℝ (Space D)) (K J : Finset (Fin T))
    (hJ : J⊆Finset.univ\K)
    (hPS : domain P≤S) (hFS : F≤S) (hKsrc : ∀ i∈K,V i∈S)
    (hPW : range P≤Wlocal) (hKdst : ∀ i∈K,O • V i∈Wlocal)
    (hW : Wlocal≤Wglobal) {z : ℝ}
    (hsource : frameEnergy S V (Finset.univ\K)≤z)
    (hlocal : frameEnergy Wlocal (fun i => O • V i) (Finset.univ\K)≤z)
    (hglobal : frameEnergy Wglobal (fun i => O • V i) J≤z)
    (hsmall : z≤(1:ℝ)/4096)
    (hgood : ¬TransportControllerEdge.angleBad Wglobal
      (residualSpace (domain (TransportRound.framePairs V O++P))
        (residualSpace (protectedDomain V P K) F)) O) :
    frameEnergy (Wlocal⊔F.map (isometry D O).toLinearEquiv.toLinearMap)
      (fun i => O • V i) (Finset.univ\K)≤17*z ∧
    frameEnergy (Wglobal⊔F.map (isometry D O).toLinearEquiv.toLinearMap)
      (fun i => O • V i) J≤17*z ∧
    protectedDomain V P K⊔F≤S ∧
    (protectedDomain V P K⊔F).map (isometry D O).toLinearEquiv.toLinearMap≤
      Wlocal⊔F.map (isometry D O).toLinearEquiv.toLinearMap := by
  have hgoodLocal := good_angle_smaller_destination Wlocal Wglobal _ O hW hgood
  have hl := TransportRound.frame_block_energy V hV O P hP S F Wlocal K (Finset.univ\K)
    (fun _ hi => hi) hPS hFS hKsrc hPW hKdst hsource hsmall hgoodLocal
  have hg := TransportRound.frame_block_energy V hV O P hP S F Wglobal K J
    hJ hPS hFS hKsrc (hPW.trans hW) (fun i hi => hW (hKdst i hi)) hsource hsmall hgood
  have hA := protectedDomain_le V P K S hPS hKsrc
  have hB := TransportRound.frame_protectedDomain_image_le V O P K Wlocal hP hPW hKdst
  refine ⟨?_,?_,sup_le hA hFS,?_⟩
  · linarith
  · linarith
  · rw [Submodule.map_sup]
    exact sup_le (hB.trans le_sup_left) le_sup_right

/-- A maximum majorant, unlike a total-energy ledger, does not pay a
factor for unchanged global, local, old or frozen rows. -/
def Majorized {ι : Type*} (E : ι → ℝ) (z : ℝ) : Prop := ∀ i,E i≤z

theorem simultaneous_update_maximum {ι : Type*} [DecidableEq ι]
    (E : ι → ℝ) (i j : ι) (a b z factor : ℝ)
    (hE : Majorized E z) (hz : 0≤z) (hf : 1≤factor)
    (ha : a≤factor*z) (hb : b≤factor*z) :
    Majorized (Function.update (Function.update E i a) j b) (factor*z) := by
  intro k
  by_cases hkj : k=j
  · subst k
    simp only [Function.update_self]
    exact hb
  · rw [Function.update_of_ne hkj]
    by_cases hki : k=i
    · subst k
      simp only [Function.update_self]
      exact ha
    · rw [Function.update_of_ne hki]
      exact (hE k).trans (by nlinarith)

theorem innovation_exact {D : ℕ} {ι : Type*} (W : Submodule ℝ (Space D)) (V : ι → Space D)
    (I : Finset ι) (u : Space D) (hu : u∈Wᗮ) (hn : ‖u‖=1) :
    frameEnergy (W⊔Submodule.span ℝ {u}) V I=
      frameEnergy W V I+∑ i∈I,inner (𝕜:=ℝ) u (V i)^2 := by
  have ht := query_energy_increment W V I u hu hn
  linarith

theorem virtual_response_no_new_direction {D : ℕ}
    (W : Submodule ℝ (Space D)) (r : Space D) (hr : r∈W) :
    W⊔Submodule.span ℝ {r}=W := by
  apply sup_eq_left.mpr
  exact (Submodule.span_singleton_le_iff_mem r W).mpr hr

end Bilevel.PolishedTransportMaximum
