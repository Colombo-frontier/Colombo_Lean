import Bilevel.ChiRecursiveNodeDerivative
import Bilevel.ChiBoundedChainSelectorJets

/-! Finite Hilbert-product realization of the actual recursive carriers.
All derivatives here are joint derivatives in all lower blocks. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Blocks (m : ℕ) (E : Type*) [NormedAddCommGroup E] := PiLp 2 (fun _ : Fin m => E)

/-- Zero padding realizes the source's finitely used sequence of blocks. -/
def block (m j : ℕ) : Blocks m E →L[ℝ] E :=
  if h : j<m then PiLp.proj 2 (fun _ : Fin m => E) ⟨j,h⟩ else 0

omit [CompleteSpace E] in
theorem block_norm_le (m j : ℕ) : ‖block (E:=E) m j‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  unfold block
  split_ifs with h
  · simpa only [one_mul,PiLp.proj_apply] using PiLp.norm_apply_le x (⟨j,h⟩:Fin m)
  · simp

def padded {m : ℕ} (x : Blocks m E) (j : ℕ) : E := block m j x

def jointH (m j : ℕ) (D : Node E) : Blocks m E → ℝ := D.H ∘ block m j
def jointSelector (m j : ℕ) (D : Node E) (i : Fin (D.n+1)) : Blocks m E → ℝ :=
  D.selector i ∘ block m j
def jointResidual (m j : ℕ) (D : Node E) (i : Fin (D.n+1)) : Blocks m E → ℝ :=
  D.residual i ∘ block m j
def jointRelease (m j : ℕ) (D : Node E) : Blocks m E → ℝ := D.release ∘ block m j

def jointPayload (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (x : Blocks m E) : ℝ :=
  payloadValue D d j I (padded x)

def jointCarrier (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (k : ℕ) (x : Blocks m E) : ℝ :=
  selectedCarrier D d j I k (padded x)

theorem jointH_contDiff (m j : ℕ) (D : Node E) (k : ℕ) : ContDiff ℝ k (jointH m j D) :=
  (D.H_contDiff k).comp (block (E:=E) m j).contDiff

theorem jointSelector_contDiff (m j : ℕ) (D : Node E) (i : Fin (D.n+1)) (k : ℕ) :
    ContDiff ℝ k (jointSelector m j D i) := (D.selector_contDiff i k).comp (block (E:=E) m j).contDiff

theorem jointResidual_contDiff (m j : ℕ) (D : Node E) (i : Fin (D.n+1)) (k : ℕ) :
    ContDiff ℝ k (jointResidual m j D i) := (D.residual_contDiff i k).comp (block (E:=E) m j).contDiff

theorem jointRelease_contDiff (m j : ℕ) (D : Node E) (k : ℕ) : ContDiff ℝ k (jointRelease m j D) :=
  (D.release_contDiff k).comp (block (E:=E) m j).contDiff

theorem jointPayload_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (k : ℕ) :
    ContDiff ℝ k (jointPayload m D d j I) := by
  induction d generalizing j I with
  | zero => exact (jointH_contDiff m j (D j I) k).sub contDiff_const
  | succ d ih =>
    exact (((jointH_contDiff m j (D j I) k).sub
      (ContDiff.sum (fun i _ => jointResidual_contDiff m j (D j I) i k))).add
      (ContDiff.sum (fun i _ => (jointResidual_contDiff m j (D j I) i k).mul
        (jointRelease_contDiff m (j+1) (D (j+1) (child I i.val)) k)))).add
      (ContDiff.sum (fun i _ => (jointSelector_contDiff m j (D j I) i k).mul (ih (j+1) (child I i.val))))

theorem jointCarrier_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (k q : ℕ) :
    ContDiff ℝ q (jointCarrier m D d j I k) := by
  induction d generalizing j I k with
  | zero =>
    cases k with
    | zero => exact (jointH_contDiff m j (D j I) q).sub contDiff_const
    | succ k => exact contDiff_const
  | succ d ih =>
    cases k with
    | zero =>
      exact ((jointH_contDiff m j (D j I) q).sub
        (ContDiff.sum (fun i _ => jointResidual_contDiff m j (D j I) i q))).add
        (ContDiff.sum (fun i _ => (jointResidual_contDiff m j (D j I) i q).mul
          (jointRelease_contDiff m (j+1) (D (j+1) (child I i.val)) q)))
    | succ k =>
      change ContDiff ℝ q (fun x => ∑ i : Fin ((D j I).n+1),
        jointSelector m j (D j I) i x*jointCarrier m D d (j+1) (child I i.val) k x)
      exact ContDiff.sum (fun i _ => (jointSelector_contDiff m j (D j I) i q).mul
        (ih (j+1) (child I i.val) k))

theorem jointPayload_trace (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    jointPayload m D d j I x=∑ k : Fin (d+1),jointCarrier m D d j I k.val x :=
  payloadValue_trace D d j I (padded x)

omit [CompleteSpace E] in
theorem block_jet_contraction (m j : ℕ) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (x : Blocks m E) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (f ∘ block m j) x‖≤‖iteratedFDeriv ℝ k f (block m j x)‖ := by
  rw [(block m j).iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg (block (E:=E) m j)) (block_norm_le m j)) (norm_nonneg _)

theorem jointSelector_jet_latent (m j : ℕ) (D : Node E) (i : Fin (D.n+1))
    (x : Blocks m E) (k : ℕ) (hk : k≤3)
    (hi : iteratedFDeriv ℝ k (jointSelector m j D i) x≠0) :
    ∃ q≤k,iteratedFDeriv ℝ q (ChiBoundedChain.selector D.n i)
      (D.width⁻¹ • D.coordinates (block m j x))≠0 := by
  by_contra! hzero
  apply hi
  have hc : ContDiff ℝ 3 (fun y : Blocks m E => D.width⁻¹ • D.coordinates (block m j y)) :=
    (((D.coordinates_contDiff 3).comp (block (E:=E) m j).contDiff).const_smul D.width⁻¹)
  exact flat_jet_comp hc (selector_contDiff D.n 3 i) x k hk
    (fun q hq => by rw [hzero q hq,norm_zero])

theorem jointSelector_jets_unique (m j : ℕ) (D : Node E) (i l : Fin (D.n+1))
    (x : Blocks m E) (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (jointSelector m j D i) x≠0)
    (hl : iteratedFDeriv ℝ q (jointSelector m j D l) x≠0) : i=l := by
  obtain ⟨a,ha,hai⟩ := jointSelector_jet_latent m j D i x k hk hi
  obtain ⟨b,hb,hbl⟩ := jointSelector_jet_latent m j D l x q hq hl
  exact selector_jets_unique i l _ a b (by omega) (by omega) hai hbl

theorem selected_product_jet_selector (m j : ℕ) (D : Node E) (i : Fin (D.n+1))
    {f : Blocks m E → ℝ} (hf : ContDiff ℝ 3 f) (x : Blocks m E) (k : ℕ) (hk : k≤3)
    (hi : iteratedFDeriv ℝ k (fun y => jointSelector m j D i y*f y) x≠0) :
    ∃ q≤k,iteratedFDeriv ℝ q (jointSelector m j D i) x≠0 := by
  by_contra! hzero
  exact hi (ZeroChainResidualBounds.jet_mul_zero_left (jointSelector_contDiff m j D i 3) hf x k hk hzero)

theorem selected_products_jets_unique (m j : ℕ) (D : Node E) (i l : Fin (D.n+1))
    {f g : Blocks m E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : Blocks m E) (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (fun y => jointSelector m j D i y*f y) x≠0)
    (hl : iteratedFDeriv ℝ q (fun y => jointSelector m j D l y*g y) x≠0) : i=l := by
  obtain ⟨a,ha,hai⟩ := selected_product_jet_selector m j D i hf x k hk hi
  obtain ⟨b,hb,hbl⟩ := selected_product_jet_selector m j D l hg x q hq hl
  exact jointSelector_jets_unique m j D i l x a b (by omega) (by omega) hai hbl

/-- Actual constructed selectors prevent a stage-count factor, even when the
selected functions depend jointly on all current and descendant blocks. -/
theorem selected_products_jet_bound (m j : ℕ) (D : Node E)
    (f : Fin (D.n+1) → Blocks m E → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (x : Blocks m E) (k : ℕ) (hk : k≤3) (B : ℝ) (hB : 0≤B)
    (hb : ∀ i,‖iteratedFDeriv ℝ k (fun y => jointSelector m j D i y*f i y) x‖≤B) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ i : Fin (D.n+1),jointSelector m j D i y*f i y) x‖≤B := by
  rw [iteratedFDeriv_sum (fun i _ => ((jointSelector_contDiff m j D i 3).mul (hf i)).of_le
    (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  apply norm_sum_le_of_exclusive _ B hB hb
  intro i l hil hi
  by_contra hl
  exact hil (selected_products_jets_unique m j D i l (hf i) (hf l) x k k hk hk hi hl)

end Bilevel.ChiCarrier
