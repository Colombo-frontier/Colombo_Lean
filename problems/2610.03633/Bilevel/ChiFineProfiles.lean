import Bilevel.ChiBoundedChainSelectorJets
import Bilevel.ZeroChainFlatteningAnnulus

/-! Incoming-coordinate profiles for the revised centered frontier. The
selectors are the actual bounded-chain selectors, not the older signed-edge
residual. Jet bounds use disjointness, hence have no chain-length factor. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainPotential
open ZeroChainResidualBounds (projection_norm_le scalar_linear_jet_bound jet_mul_bound
  jet_mul_zero_left jet_mul_zero_right)

def term (n : ℕ) (f : ℝ → ℝ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  selector n i z*f (z i)

def selected (n : ℕ) (f : ℝ → ℝ) (z : Space n) : ℝ :=
  ∑ i : Fin (n+1),term n f i z

theorem term_contDiff (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin (n+1)) : ContDiff ℝ 3 (term n f i) :=
  (selector_contDiff n 3 i).mul (hf.comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)

theorem selected_contDiff (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 3 (selected n f) := ContDiff.sum (fun i _ => term_contDiff n hf i)

theorem selected_sub (n : ℕ) (f g : ℝ → ℝ) (z : Space n) :
    selected n f z-selected n g z=selected n (fun t => f t-g t) z := by
  simp only [selected,term,mul_sub,Finset.sum_sub_distrib]

theorem centered_eq_selected (n : ℕ) :
    centeredResidual n=selected n (fun t => -(phi t-phi 0)) := by
  funext z
  apply Finset.sum_congr rfl
  intro i _
  dsimp [term]
  ring

theorem selected_abs_bound (n : ℕ) {f : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : ∀ t,|f t|≤C) (z : Space n) : |selected n f z|≤C := by
  calc
    _ ≤ ∑ i : Fin (n+1),|term n f i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n+1),selector n i z*C := by
      apply Finset.sum_le_sum
      intro i _
      rw [term,abs_mul,abs_of_nonneg (selector_range n i z).1]
      exact mul_le_mul_of_nonneg_left (hf _) (selector_range n i z).1
    _ = (∑ i : Fin (n+1),selector n i z)*C := (Finset.sum_mul ..).symm
    _ ≤ C := by nlinarith [selector_sum_le_one n z]

theorem term_jet_selector (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (term n f i) z≠0) :
    ∃ j≤k,iteratedFDeriv ℝ j (selector n i) z≠0 := by
  by_contra! h
  exact hn (jet_mul_zero_left (selector_contDiff n 3 i)
    (hf.comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff) z k hk h)

theorem term_jets_unique (n : ℕ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (i j : Fin (n+1)) (z : Space n) (k l : ℕ) (hk : k≤3) (hl : l≤3)
    (hi : iteratedFDeriv ℝ k (term n f i) z≠0)
    (hj : iteratedFDeriv ℝ l (term n g j) z≠0) : i=j := by
  obtain ⟨a,ha,hai⟩ := term_jet_selector n hf i z k hk hi
  obtain ⟨b,hb,hbj⟩ := term_jet_selector n hg j z l hl hj
  exact selector_jets_unique i j z a b (by omega) (by omega) hai hbj

theorem selected_jet_sum (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Space n) (k : ℕ) (hk : k≤3) :
    iteratedFDeriv ℝ k (selected n f) z=
      ∑ i : Fin (n+1),iteratedFDeriv ℝ k (term n f i) z := by
  have hh := congrFun (iteratedFDeriv_sum (u:=Finset.univ)
    (fun i _ => (term_contDiff n hf i).of_le (by exact_mod_cast hk))) z
  simpa only [Finset.sum_apply] using hh

theorem selected_jet_bound (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (A B : ℕ → ℝ) (hA : ∀ j,0≤A j)
    (hsel : ∀ i z j,j≤3 → ‖iteratedFDeriv ℝ j (selector n i) z‖≤A j)
    (hprof : ∀ j,j≤3 → ∀ t,|iteratedDeriv j f t|≤B j)
    (z : Space n) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (selected n f) z‖≤
      ∑ j ∈ Finset.range (k+1),(k.choose j:ℝ)*A j*B (k-j) := by
  have hB (j : ℕ) (hj : j≤3) : 0≤B j := (abs_nonneg _).trans (hprof j hj 0)
  rw [selected_jet_sum n hf z k hk]
  apply norm_sum_le_of_exclusive
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (by positivity) (hA j)) (hB _ (by omega))
  · intro i
    exact jet_mul_bound (selector_contDiff n 3 i)
      (hf.comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff) z k hk A B hA
      (fun j hj => hsel i z j (by omega))
      (fun j hj => scalar_linear_jet_bound hf _ (projection_norm_le i) z j (by omega)
        (B j) (hB j (by omega)) (hprof j (by omega) _))
  · intro i j hij hi
    by_contra hj
    exact hij (term_jets_unique n hf hf i j z k k hk hk hi hj)

theorem term_flat_profile (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k≤3)
    (hz : ∀ j,j≤k → iteratedDeriv j f (z i)=0) :
    iteratedFDeriv ℝ k (term n f i) z=0 :=
  jet_mul_zero_right (selector_contDiff n 3 i)
    (hf.comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff) z k hk
    (fun j hj => ZeroChainFlatteningAnnulus.scalar_coordinate_jet_zero hf i z j (by omega) (hz j hj))

end Bilevel.ChiFine
