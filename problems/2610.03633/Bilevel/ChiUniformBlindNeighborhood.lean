import Bilevel.ChiProjectionStability

/-! A uniform positive coordinate margin gives a genuine common open
neighborhood even for a countable totalized node family. -/
noncomputable section
open scoped Topology
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive PrimitiveGeometry ChiCarrier ChiOuter ChiExtension
variable {X E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem coordinate_linear_difference_bound (D : Node E) (hR : 0<D.radius)
    (L : X →L[ℝ] E) (hL : ‖L‖≤1) (x y : X) (k : Fin (D.n+1)) :
    |D.coordinates (L x) k-D.coordinates (L y) k|≤‖x-y‖ := by
  apply (D.coordinate_difference_bound hR _ _ k).trans
  rw [← map_sub]
  exact (L.le_opNorm (x-y)).trans (by nlinarith [norm_nonneg (x-y)])

theorem eventually_blind_uniform {ι : Type*} (D : ι → Node E)
    (hR : ∀ i,0<(D i).radius) (L : ι → X →L[ℝ] E) (hL : ∀ i,‖L i‖≤1)
    (r : ι → ℕ) (τ : ι → ℝ) (δ : ℝ) (hδ : 0<δ) (x : X)
    (hx : ∀ i,∀ k : Fin ((D i).n+1),r i≤k.val → |(D i).coordinates (L i x) k|≤τ i-δ) :
    ∀ᶠ y in 𝓝 x,∀ i,∀ k : Fin ((D i).n+1),r i≤k.val → |(D i).coordinates (L i y) k|≤τ i := by
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  intro i k hk
  have hdist : ‖y-x‖<δ := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  have hd := coordinate_linear_difference_bound (D i) (hR i) (L i) (hL i) y x k
  have ha := abs_add_le ((D i).coordinates (L i y) k-(D i).coordinates (L i x) k)
    ((D i).coordinates (L i x) k)
  rw [sub_add_cancel] at ha
  have hh := hx i k hk
  linarith

def fullTangential (m s : ℕ) : Full (Joint E (Blocks m F)) s →L[ℝ] Joint E (Blocks m F) :=
  (ContinuousLinearMap.fst ℝ (Joint E (Blocks m F)) (Normals s)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Joint E (Blocks m F)) (Normals s)).toContinuousLinearMap

omit [CompleteSpace E] [CompleteSpace F] in
theorem fullTangential_norm_le (m s : ℕ) : ‖fullTangential (E:=E) (F:=F) m s‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  exact (WithLp.norm_fst_le (Joint E (Blocks m F)) z).trans_eq (one_mul _).symm

def fullMacro (m s : ℕ) : Full (Joint E (Blocks m F)) s →L[ℝ] E :=
  (outerProjection m).comp (fullTangential m s)

def fullBlock (m s j : ℕ) : Full (Joint E (Blocks m F)) s →L[ℝ] F :=
  (hierarchyBlock m j).comp (fullTangential m s)

omit [CompleteSpace E] [CompleteSpace F] in
theorem fullMacro_norm_le (m s : ℕ) : ‖fullMacro (E:=E) (F:=F) m s‖≤1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (outerProjection_norm_le (E:=E) (F:=F) m) (fullTangential_norm_le (E:=E) (F:=F) m s)
    (norm_nonneg (fullTangential (E:=E) (F:=F) m s)) zero_le_one).trans_eq (one_mul _)

omit [CompleteSpace E] [CompleteSpace F] in
theorem fullBlock_norm_le (m s j : ℕ) : ‖fullBlock (E:=E) (F:=F) m s j‖≤1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (hierarchyBlock_norm_le (E:=E) (F:=F) m j) (fullTangential_norm_le (E:=E) (F:=F) m s)
    (norm_nonneg (fullTangential (E:=E) (F:=F) m s)) zero_le_one).trans_eq (one_mul _)

end Bilevel.ChiPrefixEvaluation
