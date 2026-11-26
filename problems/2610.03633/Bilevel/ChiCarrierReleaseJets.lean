import Bilevel.ChiCarrierNodeJets
import Bilevel.ChiRecursiveValue

/-! Actual joint jets of the recursive release correction. The one-active
selector theorem removes the number of child stages from the bound. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

theorem same_width_product_jets {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (B C h : ℝ) (hB : 0≤B) (hC : 0≤C) (hh : 0<h) (x : X) (k : ℕ) (hk : k≤3)
    (hb : ∀ q,q≤k → ‖iteratedFDeriv ℝ q f x‖≤B/h^q)
    (hc : ∀ q,q≤k → ‖iteratedFDeriv ℝ q g x‖≤C/h^q) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖≤8*B*C/h^k := by
  have hs := ZeroChainResidualBounds.jet_mul_bound hf hg x k hk
    (fun q => B/h^q) (fun q => C/h^q) (fun _ => by positivity) hb hc
  have he : (∑ q ∈ Finset.range (k+1),(k.choose q:ℝ)*(B/h^q)*(C/h^(k-q)))=
      (∑ q ∈ Finset.range (k+1),(k.choose q:ℝ))*(B*C/h^k) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    have hqk : q≤k := by have := Finset.mem_range.mp hq;omega
    have hp : h^q*h^(k-q)=h^k := by rw [← pow_add,Nat.add_sub_of_le hqk]
    calc
      _ = (k.choose q:ℝ)*(B*C)/(h^q*h^(k-q)) := by ring
      _ = _ := by rw [hp];ring
  rw [he] at hs
  have hsum : (∑ q ∈ Finset.range (k+1),(k.choose q:ℝ))≤8 := by
    interval_cases k <;> norm_num [Finset.sum_range_succ]
  have hbound := mul_le_mul_of_nonneg_right hsum (show 0≤B*C/h^k by positivity)
  exact hs.trans (by convert hbound using 1;ring)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def jointIncomingFactor (m j : ℕ) (D : Node E) (i : Fin (D.n+1)) (x : Blocks m E) : ℝ :=
  -(D.ell*D.width^2)*ZeroChainPotential.phi (D.coordinates (block m j x) i/D.width)

theorem jointIncomingFactor_contDiff (m j : ℕ) (D : Node E) (i : Fin (D.n+1)) :
    ContDiff ℝ 3 (jointIncomingFactor m j D i) :=
  contDiff_const.mul ((ZeroChainPotential.phi_contDiff 3).comp
    ((((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp (D.coordinates_contDiff 3)).comp
      (block (E:=E) m j).contDiff).div_const D.width))

theorem jointResidual_factor (m j : ℕ) (D : Node E) (i : Fin (D.n+1)) (x : Blocks m E) :
    jointResidual m j D i x=jointSelector m j D i x*jointIncomingFactor m j D i x := by
  change Rterm D.n D.ell D.width i (D.coordinates (block m j x))=_
  rw [Rterm_formula]
  dsimp [jointSelector,Node.selector,jointIncomingFactor]
  ring

def releaseCorrection (m j : ℕ) (D : Node E) (child : Fin (D.n+1) → Node E) (x : Blocks m E) : ℝ :=
  ∑ i : Fin (D.n+1),jointResidual m j D i x*(jointRelease m (j+1) (child i) x-1)

theorem releaseCorrection_contDiff (m j : ℕ) (D : Node E) (child : Fin (D.n+1) → Node E) :
    ContDiff ℝ 3 (releaseCorrection m j D child) :=
  ContDiff.sum (fun i _ => (jointResidual_contDiff m j D i 3).mul
    ((jointRelease_contDiff m (j+1) (child i) 3).sub contDiff_const))

theorem releaseCorrection_selected (m j : ℕ) (D : Node E) (child : Fin (D.n+1) → Node E) :
    releaseCorrection m j D child=fun x => ∑ i : Fin (D.n+1),
      jointSelector m j D i x*(jointIncomingFactor m j D i x*(jointRelease m (j+1) (child i) x-1)) := by
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [jointResidual_factor]
  ring

theorem jointCarrier_local_formula (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) :
    jointCarrier m D (d+1) j I 0=fun x => jointH m j (D j I) x+
      releaseCorrection m j (D j I) (fun i => D (j+1) (child I i.val)) x := by
  funext x
  simp only [jointCarrier,selectedCarrier,jointH,Function.comp_apply,padded,releaseCorrection,
    jointResidual,jointRelease,mul_sub,mul_one,Finset.sum_sub_distrib]
  ring

theorem release_sub_one_jet_bound (m j : ℕ) (D : Node E) (C h : ℝ) (hC : 1≤C)
    (x : Blocks m E) (k : ℕ) (hk : k≤3)
    (hb : ‖iteratedFDeriv ℝ k (jointRelease m j D) x‖≤C/h^k) :
    ‖iteratedFDeriv ℝ k (fun y => jointRelease m j D y-1) x‖≤C/h^k := by
  by_cases hk0 : k=0
  · subst k
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one]
    have hq := D.release_range (block m j x)
    apply le_trans _ hC
    apply abs_le.mpr
    change -1≤D.release (block m j x)-1 ∧ D.release (block m j x)-1≤1
    constructor <;> linarith only [hq.1,hq.2]
  · rw [ZeroChainCarry.jet_sub_constant (jointRelease_contDiff m j D 3) 1 x k (by omega) hk]
    exact hb

theorem constructed_release_correction_jets : ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F) (child : Fin (D.n+1) → Node F),
      0≤D.ell → 0<D.width → D.width≤D.radius → 0<D.parentWidth → D.parentWidth≤D.radius →
      (∀ i,0≤(child i).ell) → (∀ i,0<(child i).width) → (∀ i,(child i).width≤(child i).radius) →
      (∀ i,(child i).parentWidth=D.width) → (∀ i,D.width≤(child i).radius) →
      ∀ (m j : ℕ) (x : Blocks m F) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (releaseCorrection m j D child) x‖≤C*(D.ell*D.width^2)/D.width^k := by
  obtain ⟨C,hC,hb⟩ := constructed_joint_node_jets
  have hC0 : 0≤C := by linarith
  refine ⟨8*C^2,by nlinarith [sq_nonneg (C-1)],fun F _ _ _ D kids hell hh hhR hhp hhpR
    hcell hch hchR hcparent hcR m j x k hk => ?_⟩
  let f := fun i : Fin (D.n+1) => fun y : Blocks m F =>
    jointIncomingFactor m j D i y*(jointRelease m (j+1) (kids i) y-1)
  have hf (i : Fin (D.n+1)) : ContDiff ℝ 3 (f i) :=
    (jointIncomingFactor_contDiff m j D i).mul ((jointRelease_contDiff m (j+1) (kids i) 3).sub contDiff_const)
  rw [releaseCorrection_selected]
  apply selected_products_jet_bound m j D f hf x k hk _ (by positivity)
  intro i
  have he : (fun y => jointSelector m j D i y*f i y)=
      fun y => jointResidual m j D i y*(jointRelease m (j+1) (kids i) y-1) := by
    funext y
    rw [jointResidual_factor]
    dsimp [f]
    ring
  rw [he]
  have hres (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (jointResidual m j D i) x‖≤(C*(D.ell*D.width^2))/D.width^q :=
    (hb F D hell hh hhR hhp hhpR m j i x q (by omega)).2.1
  have hrel (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y => jointRelease m (j+1) (kids i) y-1) x‖≤C/D.width^q := by
    apply release_sub_one_jet_bound m (j+1) (kids i) C D.width hC x q (by omega)
    have hz := (hb F (kids i) (hcell i) (hch i) (hchR i) (by rw [hcparent i];exact hh)
      (by rw [hcparent i];exact hcR i) m (j+1) 0 x q (by omega)).2.2
    simpa only [hcparent i] using hz
  have hs := same_width_product_jets (jointResidual_contDiff m j D i 3)
    ((jointRelease_contDiff m (j+1) (kids i) 3).sub contDiff_const)
    (C*(D.ell*D.width^2)) C D.width (by positivity) hC0 hh x k hk hres hrel
  convert hs using 1
  ring

end Bilevel.ChiCarrier
