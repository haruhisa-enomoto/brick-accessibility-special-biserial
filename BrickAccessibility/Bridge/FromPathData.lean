module

public import BrickAccessibility.Bridge.Presentation
public import BrickAccessibility.StringQuotient.Chains

/-!
# From path data to an admissible presentation

Path data `D` on `Λᵐᵒᵖ` whose paths span, which is admissible, and whose vertices and arrows
are linearly independent modulo paths of length at least two, define an admissible bound
quiver presentation `π : kQ → Λ` sending `e_v ↦ e_v` and `a ↦ α_a` (`toPresentation`). If
`D` is special biserial, so is the presentation (`isSpecialBiserial_of_pathData`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Statement MulOpposite

universe u

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]
variable {Q : FinQuiver} (D : PathData Q Λᵐᵒᵖ)

namespace PathData

/-- The algebra map `kQ → Λ` of path data on `Λᵐᵒᵖ`. -/
def presMap : Q.PathAlgebra k →ₐ[k] Λ :=
  FinQuiver.liftOfRelations (k := k) (fun v ↦ (D.e v).unop) (fun a ↦ (D.α a).unop)
    (fun v w ↦ by
      rw [← unop_mul, D.e_mul_e]
      by_cases h : v = w
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h, unop_zero])
    (by
      rw [show ∑ v, (D.e v).unop = (∑ v, D.e v).unop from
        (map_sum (opAddEquiv : Λ ≃+ Λᵐᵒᵖ).symm _ _).symm, D.sum_e, unop_one])
    (fun a ↦ by rw [← unop_mul, D.α_mul_e])
    (fun a ↦ by rw [← unop_mul, D.e_mul_α])

theorem presMap_vertex (v : Q.V) : D.presMap (k := k) (Q.vertex k v) = (D.e v).unop :=
  FinQuiver.liftOfRelations_vertex _ _ _ _ _ _ v

theorem presMap_arrow (a : Q.A) : D.presMap (k := k) (Q.arrow k a) = (D.α a).unop :=
  FinQuiver.liftOfRelations_arrow _ _ _ _ _ _ a

theorem presMap_path : ∀ (l : List Q.A) (x : Q.V),
    op (D.presMap (k := k) (Q.vertex k x * Q.word k l)) = D.pval x l
  | [], x => by
      rw [FinQuiver.word_nil, mul_one, presMap_vertex, op_unop]; rfl
  | a :: l, x => by
      have ih := presMap_path l (Q.tgt a)
      rw [FinQuiver.word_cons, ← FinQuiver.arrow_mul_vertex_tgt k Q a, mul_assoc (Q.arrow k a),
        ← mul_assoc, map_mul, map_mul, op_mul, ih, op_mul, presMap_vertex, presMap_arrow,
        op_unop, op_unop]
      show _ = D.pval (Q.tgt a) l * D.α a * D.e x
      rw [mul_assoc]

theorem presMap_word (l : List Q.A) :
    op (D.presMap (k := k) (Q.word k l)) = ∑ x, D.pval x l := by
  have h1 : Q.word k l = ∑ x, Q.vertex k x * Q.word k l := by
    rw [← Finset.sum_mul, FinQuiver.sum_vertex, one_mul]
  rw [h1, map_sum]
  show (opAddEquiv : Λ ≃+ Λᵐᵒᵖ) (∑ x, _) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ ↦ D.presMap_path (k := k) l x

variable (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
  (hadm : D.IsAdmissible)
  (hind : ∀ (c : Q.V → k) (d : Q.A → k),
    ∑ v, c v • D.e v + ∑ a, d a • D.α a ∈ D.RadGe k 2 → c = 0 ∧ d = 0)

include hspan in
theorem presMap_surjective : Function.Surjective (D.presMap (k := k)) := by
  intro y
  set S := LinearMap.range (D.presMap (k := k)).toLinearMap
  have hle : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) ≤
      S.map (opLinearEquiv k : Λ ≃ₗ[k] Λᵐᵒᵖ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨x, l⟩, rfl⟩
    exact ⟨_, ⟨Q.vertex k x * Q.word k l, rfl⟩, D.presMap_path (k := k) l x⟩
  have hy : op y ∈ S.map (opLinearEquiv k : Λ ≃ₗ[k] Λᵐᵒᵖ).toLinearMap := hle (by rw [hspan]; trivial)
  obtain ⟨z, ⟨w, rfl⟩, hz⟩ := hy
  exact ⟨w, op_injective hz⟩

/-- The words of length at least two. -/
abbrev Rsq : Submodule k (Q.PathAlgebra k) :=
  Submodule.span k {y | ∃ l : List Q.A, 2 ≤ l.length ∧ y = Q.word k l}

theorem vertex_mul_arrow (x : Q.V) (a : Q.A) :
    Q.vertex k x * Q.arrow k a = if Q.src a = x then Q.arrow k a else 0 := by
  conv_lhs => rw [← FinQuiver.vertex_src_mul_arrow k Q a, ← mul_assoc, FinQuiver.vertex_mul_vertex]
  split_ifs with h1 h2 h2
  · rw [h1]; exact FinQuiver.vertex_src_mul_arrow k Q a
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [zero_mul]

/-- Every element of `kQ` is a combination of vertices and arrows plus words of length at
least two. -/
theorem decomp_pathAlgebra (z : Q.PathAlgebra k) :
    ∃ (c : Q.V → k) (d : Q.A → k) (r : Q.PathAlgebra k), r ∈ Rsq (k := k) (Q := Q) ∧
      z = ∑ v, c v • Q.vertex k v + ∑ a, d a • Q.arrow k a + r := by
  classical
  have hz : z ∈ Submodule.span k {y | ∃ (x : Q.V) (l : List Q.A), y = Q.vertex k x * Q.word k l} := by
    rw [FinQuiver.span_vertex_mul_word]; trivial
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨x, l, rfl⟩ := hy
      rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
      · refine ⟨Pi.single x 1, 0, 0, Submodule.zero_mem _, ?_⟩
        rw [FinQuiver.word_nil, mul_one]
        simp [Pi.single_apply]
      · refine ⟨0, if Q.src a = x then Pi.single a 1 else 0, 0, Submodule.zero_mem _, ?_⟩
        rw [FinQuiver.word_cons, FinQuiver.word_nil, mul_one, vertex_mul_arrow]
        split_ifs <;> simp [Pi.single_apply]
      · refine ⟨0, 0, Q.vertex k x * Q.word k (a :: b :: l), ?_, by simp⟩
        rw [FinQuiver.word_cons, ← mul_assoc, vertex_mul_arrow]
        split_ifs
        · rw [← FinQuiver.word_cons]; exact Submodule.subset_span ⟨a :: b :: l, by simp, rfl⟩
        · rw [zero_mul]; exact Submodule.zero_mem _
  | zero => exact ⟨0, 0, 0, Submodule.zero_mem _, by simp⟩
  | add y y' _ _ hy hy' =>
      obtain ⟨c, d, r, hr, rfl⟩ := hy
      obtain ⟨c', d', r', hr', rfl⟩ := hy'
      refine ⟨c + c', d + d', r + r', Submodule.add_mem _ hr hr', ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
  | smul t y _ hy =>
      obtain ⟨c, d, r, hr, rfl⟩ := hy
      refine ⟨t • c, t • d, t • r, Submodule.smul_mem _ _ hr, ?_⟩
      simp only [Pi.smul_apply, smul_add, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem presMap_Rsq {r : Q.PathAlgebra k} (hr : r ∈ Rsq (k := k) (Q := Q)) :
    op (D.presMap (k := k) r) ∈ D.RadGe k 2 := by
  induction hr using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      rw [presMap_word]
      exact Submodule.sum_mem _ fun x _ ↦ D.pval_mem_radGe x hl
  | zero => simp
  | add y y' _ _ hy hy' => rw [map_add, op_add]; exact Submodule.add_mem _ hy hy'
  | smul t y _ hy => rw [map_smul, op_smul]; exact Submodule.smul_mem _ _ hy

include hind in
theorem ker_le_sq (z : Q.PathAlgebra k) (hz : D.presMap (k := k) z = 0) :
    z ∈ Rsq (k := k) (Q := Q) := by
  obtain ⟨c, d, r, hr, rfl⟩ := decomp_pathAlgebra (k := k) (Q := Q) z
  have hrR := D.presMap_Rsq hr
  have h0 : ∑ v, c v • D.e v + ∑ a, d a • D.α a = -op (D.presMap (k := k) r) := by
    have h2 : op (D.presMap (k := k) (∑ v, c v • Q.vertex k v + ∑ a, d a • Q.arrow k a + r)) =
        ∑ v, c v • D.e v + ∑ a, d a • D.α a + op (D.presMap (k := k) r) := by
      rw [map_add, map_add, map_sum, map_sum]
      simp only [map_smul, presMap_vertex, presMap_arrow]
      show (opAddEquiv : Λ ≃+ Λᵐᵒᵖ) (∑ v, c v • (D.e v).unop + ∑ a, d a • (D.α a).unop + _) = _
      rw [map_add, map_add, map_sum, map_sum]
      rfl
    rw [hz, op_zero] at h2
    exact eq_neg_of_add_eq_zero_left h2.symm
  obtain ⟨rfl, rfl⟩ := hind c d (h0 ▸ Submodule.neg_mem _ hrR)
  simpa using hr

include hspan hadm hind in
/-- **The admissible presentation of path data.** -/
def toPresentation : AdmissiblePresentation k Λ where
  Q := Q
  π := D.presMap (k := k)
  surjective := D.presMap_surjective hspan
  nilpotent := by
    obtain ⟨-, -, N, hN⟩ := hadm
    refine ⟨max N 2, le_max_right _ _, fun l hl ↦ op_injective ?_⟩
    rw [presMap_word, op_zero]
    exact Finset.sum_eq_zero fun x _ ↦ hN x l (by rw [hl]; exact le_max_left _ _)
  ker_le_sq := D.ker_le_sq hind

include hspan hadm hind in
theorem toPresentation_arr (a : Q.A) :
    (D.toPresentation hspan hadm hind).arr a = (D.α a).unop :=
  D.presMap_arrow a

theorem pval_pair_eq {a b : Q.A} (h : Q.src b = Q.tgt a) :
    D.pval (Q.src a) [a, b] = D.α b * D.α a := by
  show D.pval (Q.tgt a) [b] * D.α a * D.e (Q.src a) = _
  rw [← h, D.pval_single_src, mul_assoc, D.α_mul_e]

theorem allowed_iff_succ (a c : Q.A) :
    (Q.src c = Q.tgt a ∧ D.presMap (k := k) (Q.arrow k a) * D.presMap (k := k) (Q.arrow k c) ≠ 0) ↔
      D.Allowed a c := by
  rw [presMap_arrow, presMap_arrow, Allowed]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h0 ↦ h2 ?_⟩
    rw [pval_pair_eq D h1] at h0
    rw [← unop_mul, h0, unop_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h0 ↦ h2 ?_⟩
    rw [pval_pair_eq D h1, ← op_unop (D.α c * D.α a), unop_mul, h0, op_zero]

theorem allowed_iff_pred (c b : Q.A) :
    (Q.tgt c = Q.src b ∧ D.presMap (k := k) (Q.arrow k c) * D.presMap (k := k) (Q.arrow k b) ≠ 0) ↔
      D.Allowed c b := by
  rw [← D.allowed_iff_succ (k := k)]
  exact and_congr_left' eq_comm

include hspan hadm hind in
/-- **Special biserial path data give a special biserial presentation.** -/
theorem isSpecialBiserial_of_pathData (hsb : D.IsSpecialBiserial) :
    Statement.IsSpecialBiserial k Λ :=
  ⟨D.toPresentation hspan hadm hind, hsb.1, hsb.2.1,
    fun a ↦ le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun c ↦
      D.allowed_iff_succ (k := k) a c)) (hsb.2.2.1 a),
    fun b ↦ le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun c ↦
      D.allowed_iff_pred (k := k) c b)) (hsb.2.2.2 b)⟩

end PathData

end BrickAccessibility
