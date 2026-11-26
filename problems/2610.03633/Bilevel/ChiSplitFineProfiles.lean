import Bilevel.ChiSplitPayloadJets
import Bilevel.ChiFineProfiles
import Bilevel.ChiOuterCarrierSelectors

/-! Joint selector/source profiles for the split centered frontier. Selector
jets live only in predecessor coordinates, so the one-active estimate retains
its dimension-independent constant across both endpoint variables. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiSplitFine
open ChiBoundedChain ZeroChainPotential PrimitiveGeometry PartialLegendre
open ZeroChainResidualBounds (scalar_linear_jet_bound jet_mul_bound jet_mul_zero_left jet_mul_zero_right)
abbrev Latent := ChiSplitChain.Latent

def selector (n : ℕ) (i : Fin (n+1)) (z : Latent n) : ℝ := ChiBoundedChain.selector n i z.snd

def term (n : ℕ) (f : ℝ → ℝ) (i : Fin (n+1)) (z : Latent n) : ℝ := selector n i z*f (z.fst i)

def selected (n : ℕ) (f : ℝ → ℝ) (z : Latent n) : ℝ := ∑ i : Fin (n+1),term n f i z

theorem selector_contDiff (n : ℕ) (i : Fin (n+1)) : ContDiff ℝ 3 (selector n i) :=
  (ChiBoundedChain.selector_contDiff n 3 i).comp (jointSndLinear : Latent n →L[ℝ] Space n).contDiff

theorem selector_jet_zero {n : ℕ} (i : Fin (n+1)) (z : Latent n) (k : ℕ) (hk : k≤3)
    (hz : iteratedFDeriv ℝ k (ChiBoundedChain.selector n i) z.snd=0) :
    iteratedFDeriv ℝ k (selector n i) z=0 := by
  let P : Latent n →L[ℝ] Space n := jointSndLinear
  change iteratedFDeriv ℝ k (ChiBoundedChain.selector n i ∘ P) z=0
  rw [P.iteratedFDeriv_comp_right (ChiBoundedChain.selector_contDiff n 3 i) z
    (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk)]
  change (iteratedFDeriv ℝ k (ChiBoundedChain.selector n i) z.snd).compContinuousLinearMap (fun _ => P)=0
  rw [hz]
  ext v
  rfl

theorem selector_jet_bound {n : ℕ} (i : Fin (n+1)) (z : Latent n) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (selector n i) z‖≤‖iteratedFDeriv ℝ k (ChiBoundedChain.selector n i) z.snd‖ :=
  ChiOuter.contraction_jet_bound (jointSndLinear : Latent n →L[ℝ] Space n)
    ChiPrimitive.jointSndLinear_norm (ChiBoundedChain.selector_contDiff n 3 i) z k hk

theorem source_projection_norm {n : ℕ} (i : Fin (n+1)) :
    ‖(ChiSplitChain.sourceProjection i : Latent n →L[ℝ] ℝ)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [ChiSplitChain.sourceProjection_apply,Real.norm_eq_abs,one_mul] using
    (ChiSplitChain.split_coordinate_bound z i).1

theorem term_contDiff (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (i : Fin (n+1)) :
    ContDiff ℝ 3 (term n f i) :=
  (selector_contDiff n i).mul (hf.comp (ChiSplitChain.sourceProjection i).contDiff)

theorem selected_contDiff (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 3 (selected n f) := ContDiff.sum (fun i _ => term_contDiff n hf i)

theorem selected_sub (n : ℕ) (f g : ℝ → ℝ) (z : Latent n) :
    selected n f z-selected n g z=selected n (fun t => f t-g t) z := by
  simp only [selected,term,mul_sub,Finset.sum_sub_distrib]

theorem frontier_eq_selected (n : ℕ) :
    ChiSplitChain.frontier n=selected n (fun t => -(phi t-phi 0)) := by
  funext z
  apply Finset.sum_congr rfl
  intro i _
  dsimp [term,selector]
  ring

theorem selected_abs_bound (n : ℕ) {f : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : ∀ t,|f t|≤C) (z : Latent n) : |selected n f z|≤C := by
  calc
    _≤∑ i : Fin (n+1),|term n f i z| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ i : Fin (n+1),ChiBoundedChain.selector n i z.snd*C := by
      apply Finset.sum_le_sum
      intro i _
      rw [term,selector,abs_mul,abs_of_nonneg (ChiBoundedChain.selector_range n i z.snd).1]
      exact mul_le_mul_of_nonneg_left (hf _) (ChiBoundedChain.selector_range n i z.snd).1
    _=(∑ i : Fin (n+1),ChiBoundedChain.selector n i z.snd)*C := (Finset.sum_mul ..).symm
    _≤C := by nlinarith only [mul_le_mul_of_nonneg_right (ChiBoundedChain.selector_sum_le_one n z.snd) hC]

theorem term_jet_selector (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin (n+1)) (z : Latent n) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (term n f i) z≠0) :
    ∃ j≤k,iteratedFDeriv ℝ j (ChiBoundedChain.selector n i) z.snd≠0 := by
  by_contra! h
  exact hn (jet_mul_zero_left (selector_contDiff n i)
    (hf.comp (ChiSplitChain.sourceProjection i).contDiff) z k hk
      (fun j hj => selector_jet_zero i z j (by omega) (h j hj)))

theorem term_jets_unique (n : ℕ) {f g : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (i j : Fin (n+1)) (z : Latent n) (k l : ℕ) (hk : k≤3) (hl : l≤3)
    (hi : iteratedFDeriv ℝ k (term n f i) z≠0)
    (hj : iteratedFDeriv ℝ l (term n g j) z≠0) : i=j := by
  obtain ⟨a,ha,hai⟩ := term_jet_selector n hf i z k hk hi
  obtain ⟨b,hb,hbj⟩ := term_jet_selector n hg j z l hl hj
  exact ChiBoundedChain.selector_jets_unique i j z.snd a b (by omega) (by omega) hai hbj

theorem selected_jet_sum (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Latent n) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (selected n f) z=∑ i : Fin (n+1),iteratedFDeriv ℝ k (term n f i) z := by
  have hh := congrFun (iteratedFDeriv_sum (u:=Finset.univ)
    (fun i _ => (term_contDiff n hf i).of_le (by exact_mod_cast hk))) z
  simpa only [Finset.sum_apply] using hh

theorem selected_jet_bound (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (A B : ℕ → ℝ) (hA : ∀ j,0≤A j)
    (hsel : ∀ i z j,j≤3 → ‖iteratedFDeriv ℝ j (ChiBoundedChain.selector n i) z‖≤A j)
    (hprof : ∀ j,j≤3 → ∀ t,|iteratedDeriv j f t|≤B j) (z : Latent n) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (selected n f) z‖≤∑ j ∈ Finset.range (k+1),(k.choose j:ℝ)*A j*B (k-j) := by
  have hB (j : ℕ) (hj : j≤3) : 0≤B j := (abs_nonneg _).trans (hprof j hj 0)
  rw [selected_jet_sum n hf z k hk]
  apply norm_sum_le_of_exclusive
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (by positivity) (hA j)) (hB _ (by omega))
  · intro i
    exact jet_mul_bound (selector_contDiff n i) (hf.comp (ChiSplitChain.sourceProjection i).contDiff)
      z k hk A B hA (fun j hj => (selector_jet_bound i z j (by omega)).trans (hsel i z.snd j (by omega)))
      (fun j hj => scalar_linear_jet_bound hf _ (source_projection_norm i) z j (by omega)
        (B j) (hB j (by omega)) (hprof j (by omega) _))
  · intro i j hij hi
    by_contra hj
    exact hij (term_jets_unique n hf hf i j z k k hk hk hi hj)

theorem term_flat_profile (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin (n+1)) (z : Latent n) (k : ℕ) (hk : k≤3)
    (hz : ∀ j,j≤k → iteratedDeriv j f (z.fst i)=0) : iteratedFDeriv ℝ k (term n f i) z=0 := by
  apply jet_mul_zero_right (selector_contDiff n i) (hf.comp (ChiSplitChain.sourceProjection i).contDiff) z k hk
  intro j hj
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply scalar_linear_jet_bound hf _ (source_projection_norm i) z j (by omega) 0 le_rfl
  simp only [ChiSplitChain.sourceProjection_apply,hz j hj,abs_zero,le_refl]

end Bilevel.ChiSplitFine
