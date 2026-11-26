import Bilevel.ChiCarrierTerminalForce
import Bilevel.WrappedPrefixLocality

/-! The terminal-block gradient of the actual selected radial leaves is
the actual radial derivative applied to the selected pre-wrapper force.
Ancestor selection is a subprobability, so this force has no depth loss. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem selectVectors_congr_leaf (m : ℕ) (D : Geometry E)
    (f g : ℕ → List ℕ → Blocks m E → E) (d j : ℕ) (I : List ℕ) (x : Blocks m E)
    (he : ∀ P,f (j+d) P x=g (j+d) P x) :
    selectVectors m D f d j I x=selectVectors m D g d j I x := by
  induction d generalizing j I with
  | zero => exact he I
  | succ d ih =>
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ih (j+1) (child I i.val) (fun P => by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he P)

theorem selectVectors_map (m : ℕ) (D : Geometry E)
    (f : ℕ → List ℕ → Blocks m E → E) (T : E →L[ℝ] E)
    (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    selectVectors m D (fun k P y => T (f k P y)) d j I x=T (selectVectors m D f d j I x) := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih => simp only [selectVectors,ih,map_sum,map_smul]

omit [CompleteSpace E] in
theorem wrappedGradient_zero_eq (R : ℝ) (u h : E) :
    wrappedGradient 0 R u h=compressDerivative R u h := by
  simp only [wrappedGradient,compressDerivative_apply,zero_mul,zero_sub]
  module

def jointLatentLeaf (m j : ℕ) (D : Node E) (f : Space D.n → ℝ) : Blocks m E → ℝ :=
  (f ∘ D.coordinates) ∘ block m j

def selectedLatentForce (m : ℕ) (D : Geometry E)
    (f : ∀ k P,Space (D k P).n → ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m E) : E :=
  selectVectors m D (fun k P y => (D k P).frame
    (gradient (f k P) ((D k P).coordinates (block m k y)))) d j I x

theorem selected_radial_terminal_gradient {m : ℕ} (D : Geometry E)
    (f : ∀ k P,Space (D k P).n → ℝ) (hf : ∀ k P,ContDiff ℝ 3 (f k P))
    (d j : ℕ) (I : List ℕ) (t : Fin m) (ht : t.val=j+d)
    (R : ℝ) (hR : 0<R) (hRnode : ∀ P,(D (j+d) P).radius=R) (x : Blocks m E) :
    (gradient (selectFamily m D (fun k P => jointLatentLeaf m k (D k P) (f k P)) d j I) x) t=
      compressDerivative R (x t) (selectedLatentForce m D f d j I x) := by
  have hleaf (k : ℕ) (P : List ℕ) : ContDiff ℝ 3 (jointLatentLeaf m k (D k P) (f k P)) :=
    ((hf k P).comp ((D k P).coordinates_contDiff 3)).comp (block (E:=E) m k).contDiff
  rw [selected_gradient_terminal_block D _ hleaf d j I t ht]
  unfold selectedLatentForce
  rw [← selectVectors_map m D _ (compressDerivative R (x t)) d j I x]
  apply selectVectors_congr_leaf
  intro P
  have htm : j+d<m := by rw [← ht];exact t.isLt
  have hit : (⟨j+d,htm⟩ : Fin m)=t := Fin.ext ht.symm
  have hd := gradient_block_composition x ⟨j+d,htm⟩
    ((hf (j+d) P).comp ((D (j+d) P).coordinates_contDiff 3))
  change (gradient ((f (j+d) P ∘ (D (j+d) P).coordinates) ∘ block m (j+d)) x) t=_
  rw [hd,hit,insertion_apply,if_pos rfl]
  change gradient (f (j+d) P ∘ WrappedChain.coordinates _ (D (j+d) P).radius (D (j+d) P).frame) (x t)=_
  rw [WrappedPrefixLocality.carried_gradient _ _ (by rw [hRnode];exact hR) _ _
    ((hf (j+d) P).differentiable (by norm_num)),wrappedGradient_zero_eq]
  simp only [Node.coordinates,hRnode,block,dif_pos htm,hit,PiLp.proj_apply]

theorem selectedLatentForce_norm_le (m : ℕ) (D : Geometry E)
    (f : ∀ k P,Space (D k P).n → ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m E)
    (B : ℝ) (hB : 0≤B) (hb : ∀ P z,‖gradient (f (j+d) P) z‖≤B) :
    ‖selectedLatentForce m D f d j I x‖≤B := by
  apply selectVectors_norm_le m D _ d j I x B hB
  intro P
  rw [LinearIsometry.norm_map]
  exact hb P _

end Bilevel.ChiCarrier
