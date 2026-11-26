import GradientHessian.NalenMeasurableSelection
import GradientHessian.NalenTrajectory
import Mathlib.MeasureTheory.Constructions.Pi

/-! Literal measurable NALEN memory operations. Query-point history is
retained explicitly, so complete-block candidates are exact averages. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open MeasureTheory Set Metric Nalen
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (E →L[ℝ] E)] [BorelSpace (E →L[ℝ] E)]

abbrev Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (Fin 4 → E) × (ℕ → E) × (E →L[ℝ] E) × ℝ

def position (s : Data E) : E := s.1 0
def delta (s : Data E) : E := s.1 1
def prox (s : Data E) : E := s.1 2
def best (s : Data E) : E := s.1 3
def queries (s : Data E) : ℕ → E := s.2.1
def matrix (s : Data E) : E →L[ℝ] E := s.2.2.1
def score (s : Data E) : ℝ := s.2.2.2

def make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : Data E :=
  (![x,δ,v,b],ys,B,a)

@[simp] theorem position_make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : position (make x δ v b ys B a)=x := rfl
@[simp] theorem delta_make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : delta (make x δ v b ys B a)=δ := rfl
@[simp] theorem prox_make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : prox (make x δ v b ys B a)=v := rfl
@[simp] theorem best_make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : best (make x δ v b ys B a)=b := rfl
@[simp] theorem queries_make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : queries (make x δ v b ys B a)=ys := rfl
@[simp] theorem matrix_make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : matrix (make x δ v b ys B a)=B := rfl
@[simp] theorem score_make (x δ v b : E) (ys : ℕ → E) (B : E →L[ℝ] E) (a : ℝ) : score (make x δ v b ys B a)=a := rfl

@[measurability, fun_prop] theorem position_measurable : Measurable (position (E := E)) := (measurable_pi_apply 0).comp measurable_fst
@[measurability, fun_prop] theorem delta_measurable : Measurable (delta (E := E)) := (measurable_pi_apply 1).comp measurable_fst
@[measurability, fun_prop] theorem prox_measurable : Measurable (prox (E := E)) := (measurable_pi_apply 2).comp measurable_fst
@[measurability, fun_prop] theorem best_measurable : Measurable (best (E := E)) := (measurable_pi_apply 3).comp measurable_fst
@[measurability, fun_prop] theorem queries_measurable : Measurable (queries (E := E)) := measurable_snd.fst
@[measurability, fun_prop] theorem matrix_measurable : Measurable (matrix (E := E)) := measurable_snd.snd.fst
@[measurability, fun_prop] theorem score_measurable : Measurable (score (E := E)) := measurable_snd.snd.snd

theorem make_measurable {Ω : Type*} [MeasurableSpace Ω] {x δ v b : Ω → E} {ys : Ω → ℕ → E}
    {B : Ω → E →L[ℝ] E} {a : Ω → ℝ}
    (hx : Measurable x) (hδ : Measurable δ) (hv : Measurable v) (hb : Measurable b)
    (hy : Measurable ys) (hB : Measurable B) (ha : Measurable a) :
    Measurable (fun w => make (x w) (δ w) (v w) (b w) (ys w) (B w) (a w)) := by
  apply Measurable.prodMk _ (hy.prodMk (hB.prodMk ha))
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact hx
  · exact hδ
  · exact hv
  · exact hb

def initial (D : ℝ) (g : E) : Data E :=
  make 0 (-(D/‖g‖) • g) (-(D/‖g‖) • g) 0 (fun _ => 0) 0 ‖g‖

def snapshot (s : Data E) (B : E →L[ℝ] E) : Data E :=
  make (position s) (delta s) (prox s) (best s) (queries s) B (score s)

def predict {D : ℝ} (hD : 0≤D) (η : ℝ) (s : Data E) (g : E) : Data E :=
  make (position s) (quadraticBorelStep hD (g,matrix s,delta s,prox s,η))
    (prox s) (best s) (queries s) (matrix s) (score s)

def correct {D : ℝ} (hD : 0≤D) (η : ℝ) (n : ℕ) (s : Data E) (g : E) : Data E :=
  make (position s+delta s) (delta s) (quadraticBorelStep hD (g,0,0,prox s,η))
    (best s) (Function.update (queries s) n (midpoint (position s) (delta s))) (matrix s) (score s)

def average (q n : ℕ) (s : Data E) : E :=
  ((q:ℝ)⁻¹) • ∑ j ∈ Finset.range q,queries s (n+1-q+j)

def consider (q n : ℕ) (s : Data E) (g : E) : Data E :=
  if ‖g‖≤score s then make (position s) (delta s) (prox s) (average q n s) (queries s) (matrix s) ‖g‖ else s

theorem initial_measurable (D : ℝ) : Measurable (initial (E := E) D) := by
  apply make_measurable <;> fun_prop

theorem snapshot_measurable : Measurable (fun p : Data E × (E →L[ℝ] E) => snapshot p.1 p.2) := by
  apply make_measurable <;> fun_prop

theorem predict_measurable {D : ℝ} (hD : 0≤D) (η : ℝ) :
    Measurable (fun p : Data E × E => predict hD η p.1 p.2) := by
  apply make_measurable
  · fun_prop
  · exact quadraticBorelStep_comp_measurable hD measurable_snd
      (matrix_measurable.comp measurable_fst) (delta_measurable.comp measurable_fst)
      (prox_measurable.comp measurable_fst) measurable_const
  all_goals fun_prop

theorem correct_measurable {D : ℝ} (hD : 0≤D) (η : ℝ) (n : ℕ) :
    Measurable (fun p : Data E × E => correct hD η n p.1 p.2) := by
  apply make_measurable
  · fun_prop
  · fun_prop
  · exact quadraticBorelStep_comp_measurable hD measurable_snd measurable_const measurable_const
      (prox_measurable.comp measurable_fst) measurable_const
  · fun_prop
  · have hh : Measurable (fun p : Data E × E => (queries p.1,midpoint (position p.1) (delta p.1))) := by
      apply Measurable.prodMk
      · exact queries_measurable.comp measurable_fst
      · unfold Nalen.midpoint
        fun_prop
    exact (measurable_update' (a := n)).comp hh
  all_goals fun_prop

@[fun_prop] theorem average_measurable (q n : ℕ) : Measurable (average (E := E) q n) := by
  unfold average
  fun_prop

theorem consider_measurable (q n : ℕ) : Measurable (fun p : Data E × E => consider q n p.1 p.2) := by
  apply Measurable.ite (measurableSet_le measurable_snd.norm (score_measurable.comp measurable_fst))
  · apply make_measurable <;> fun_prop
  · exact measurable_fst

@[simp] theorem position_snapshot (s : Data E) (B : E →L[ℝ] E) : position (snapshot s B)=position s := rfl
@[simp] theorem delta_snapshot (s : Data E) (B : E →L[ℝ] E) : delta (snapshot s B)=delta s := rfl
@[simp] theorem prox_snapshot (s : Data E) (B : E →L[ℝ] E) : prox (snapshot s B)=prox s := rfl
@[simp] theorem queries_snapshot (s : Data E) (B : E →L[ℝ] E) : queries (snapshot s B)=queries s := rfl
@[simp] theorem matrix_snapshot (s : Data E) (B : E →L[ℝ] E) : matrix (snapshot s B)=B := rfl

@[simp] theorem position_consider (q n : ℕ) (s : Data E) (g : E) : position (consider q n s g)=position s := by unfold consider; split_ifs <;> rfl
@[simp] theorem delta_consider (q n : ℕ) (s : Data E) (g : E) : delta (consider q n s g)=delta s := by unfold consider; split_ifs <;> rfl
@[simp] theorem prox_consider (q n : ℕ) (s : Data E) (g : E) : prox (consider q n s g)=prox s := by unfold consider; split_ifs <;> rfl
@[simp] theorem queries_consider (q n : ℕ) (s : Data E) (g : E) : queries (consider q n s g)=queries s := by unfold consider; split_ifs <;> rfl
@[simp] theorem matrix_consider (q n : ℕ) (s : Data E) (g : E) : matrix (consider q n s g)=matrix s := by unfold consider; split_ifs <;> rfl

theorem score_consider_le (q n : ℕ) (s : Data E) (g : E) : score (consider q n s g)≤score s := by
  by_cases h : ‖g‖≤score s <;> simp [consider,h]

theorem score_consider_le_norm (q n : ℕ) (s : Data E) (g : E) : score (consider q n s g)≤‖g‖ := by
  by_cases h : ‖g‖≤score s
  · simp [consider,h]
  · simpa [consider,h] using (not_le.mp h).le

end GradientHessian.NalenPolicy
