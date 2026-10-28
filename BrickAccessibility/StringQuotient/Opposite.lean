module

public import BrickAccessibility.StringQuotient.Ideal

/-!
# Opposite path data

Path data in `A` for `Q` gives path data in `Aᵐᵒᵖ` for the opposite quiver (`opD`), with
path values the reversed ones (`pval_op`). Spanning, admissibility and the special biserial
conditions pass to it.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement MulOpposite

/-- The opposite quiver. -/
@[reducible] def Statement.FinQuiver.op (Q : FinQuiver) : FinQuiver where
  V := Q.V
  A := Q.A
  src := Q.tgt
  tgt := Q.src

theorem Statement.FinQuiver.pend_append (Q : FinQuiver) (x : Q.V) (l₁ l₂ : List Q.A) :
    Q.pend x (l₁ ++ l₂) = Q.pend (Q.pend x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons a l ih => exact ih _

theorem Statement.FinQuiver.pend_concat (Q : FinQuiver) (x : Q.V) (l : List Q.A) (a : Q.A) :
    Q.pend x (l ++ [a]) = Q.tgt a := by
  rw [Q.pend_append]; rfl

namespace PathData

variable {k : Type*} [Field k] {Q : FinQuiver} {A : Type*} [Ring A] [Algebra k A]
  (D : PathData Q A)

/-- The opposite path data. -/
def opD : PathData Q.op Aᵐᵒᵖ where
  e v := op (D.e v)
  α a := op (D.α a)
  e_mul_e v w := by
    rw [← op_mul, D.e_mul_e]
    by_cases h : v = w
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, op_zero]
  sum_e := by
    rw [show ∑ v, op (D.e v) = op (∑ v, D.e v) from (map_sum MulOpposite.opAddEquiv _ _).symm,
      D.sum_e, op_one]
  α_mul_e a := by
    show op (D.α a) * op (D.e (Q.tgt a)) = op (D.α a)
    rw [← op_mul, D.e_mul_α]
  e_mul_α a := by
    show op (D.e (Q.src a)) * op (D.α a) = op (D.α a)
    rw [← op_mul, D.α_mul_e]

/-- Path values of the opposite data are the reversed path values. -/
theorem pval_op (y : Q.V) (l : List Q.A) :
    D.opD.pval y l = op (D.e y * D.pval (Q.op.pend y l) l.reverse) := by
  induction l generalizing y with
  | nil =>
      show op (D.e y) = op (D.e y * D.e y)
      rw [D.e_idem]
  | cons a l ih =>
      show D.opD.pval (Q.src a) l * op (D.α a) * op (D.e y) = _
      rw [ih, ← op_mul, ← op_mul, List.reverse_cons, D.pval_append, D.pval_single]
      congr 1
      rw [mul_assoc (D.α a), D.e_pend_mul_pval, ← mul_assoc (D.α a) (D.e (Q.src a)), D.α_mul_e]
      rfl

theorem pend_op_reverse {x : Q.V} {l : List Q.A} (h : D.pval x l ≠ 0) :
    Q.op.pend (Q.pend x l) l.reverse = x := by
  cases l with
  | nil => rfl
  | cons a l =>
      rw [List.reverse_cons, Q.op.pend_concat]
      exact D.src_eq_of_ne h

/-- A nonzero path value is an opposite path value. -/
theorem op_pval {x : Q.V} {l : List Q.A} (h : D.pval x l ≠ 0) :
    op (D.pval x l) = D.opD.pval (Q.pend x l) l.reverse := by
  rw [pval_op, List.reverse_reverse, D.pend_op_reverse h, D.e_pend_mul_pval]

variable {D}

theorem opD_span
    (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤) :
    Submodule.span k (Set.range (fun p : Q.op.V × List Q.op.A ↦ D.opD.pval p.1 p.2)) = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  have hb : c.unop ∈ Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) := by
    rw [hspan]; trivial
  have := Submodule.mem_map_of_mem (f := (MulOpposite.opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap) hb
  rw [Submodule.map_span] at this
  refine Submodule.span_le.mpr ?_ this
  rintro _ ⟨_, ⟨⟨x, l⟩, rfl⟩, rfl⟩
  by_cases h : D.pval x l = 0
  · show op (D.pval x l) ∈ _
    rw [h, op_zero]; exact Submodule.zero_mem _
  · show op (D.pval x l) ∈ _
    rw [D.op_pval h]
    exact Submodule.subset_span ⟨(Q.pend x l, l.reverse), rfl⟩

theorem opD_adm (hadm : D.IsAdmissible) : D.opD.IsAdmissible := by
  refine ⟨fun v h ↦ hadm.1 v (op_injective h), fun a h ↦ hadm.2.1 a (op_injective h), ?_⟩
  obtain ⟨N, hN⟩ := hadm.2.2
  refine ⟨N, fun y l hl ↦ ?_⟩
  rw [pval_op, hN _ _ (by rw [List.length_reverse]; exact hl), mul_zero, op_zero]

theorem opD_allowed {a b : Q.A} : D.opD.Allowed a b ↔ D.Allowed b a := by
  have key : D.opD.pval (Q.tgt a) [a, b] = op (D.e (Q.tgt a) * D.pval (Q.src b) [b, a]) :=
    D.pval_op _ _
  have e2 : D.e (Q.tgt a) * D.pval (Q.src b) [b, a] = D.pval (Q.src b) [b, a] :=
    D.e_pend_mul_pval (Q.src b) [b, a]
  show (Q.tgt b = Q.src a ∧ D.opD.pval (Q.tgt a) [a, b] ≠ 0) ↔
    (Q.src a = Q.tgt b ∧ D.pval (Q.src b) [b, a] ≠ 0)
  rw [key, e2, Ne, op_eq_zero_iff, eq_comm]

theorem opD_sb (hsb : D.IsSpecialBiserial) : D.opD.IsSpecialBiserial := by
  refine ⟨fun x ↦ hsb.2.1 x, fun y ↦ hsb.1 y, fun a ↦ ?_, fun b ↦ ?_⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight fun b ↦ opD_allowed (D := D) (a := a) (b := b))]
    exact hsb.2.2.2 a
  · rw [Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ opD_allowed (D := D) (a := a) (b := b))]
    exact hsb.2.2.1 b

section Socle

variable (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial)
include hadm hsb

theorem reverse_eq_cons {r : List Q.A} (hr : r ≠ []) :
    r.reverse = r.getLast hr :: r.dropLast.reverse := by
  conv_lhs => rw [← List.dropLast_append_getLast hr]
  rw [List.reverse_append]; rfl

/-- A longest path that no path of positive length extends on the left is, reversed, a
longest opposite path. -/
theorem Pm_op_eq {x : Q.V} {c : Q.A} (hxc : Q.src c = x)
    (hkill : ∀ (w : Q.V) (σ : List Q.A), σ ≠ [] → D.pval x (Pm hadm c) * D.pval w σ = 0) :
    Pm (opD_adm hadm) ((Pm hadm c).getLast (List.cons_ne_nil _ _)) = (Pm hadm c).reverse := by
  set r := Pm hadm c with hr
  have hr0 : r ≠ [] := List.cons_ne_nil _ _
  set ar := r.getLast hr0
  have hne : D.pval x r ≠ 0 := pval_Pm_ne hadm hsb hxc
  have hy : Q.op.src ar = Q.pend x r := by
    show Q.tgt ar = _
    conv_rhs => rw [← List.dropLast_append_getLast hr0]
    rw [Q.pend_concat]
  have hrev := reverse_eq_cons hadm hsb hr0
  have hval : D.opD.pval (Q.pend x r) r.reverse = op (D.pval x r) := (D.op_pval hne).symm
  have hval' : D.opD.pval (Q.op.src ar) (ar :: r.dropLast.reverse) ≠ 0 := by
    rw [hy, ← hrev, hval, Ne, op_eq_zero_iff]; exact hne
  obtain ⟨v, hv⟩ := prefix_Pm (opD_adm hadm) (opD_sb hsb) hval'
  rcases List.eq_nil_or_concat v with h0 | ⟨v', d, hv'⟩
  · rw [← hv, h0, List.append_nil, hrev]
  · exfalso
    have hP := Pm_ne (opD_adm hadm) ar
    rw [← hv, hy, D.pval_op, ← hrev, List.reverse_append, List.reverse_reverse] at hP
    apply hP
    set z := Q.op.pend (Q.pend x r) (r.reverse ++ v)
    have hvr : v.reverse ≠ [] := by rw [hv', List.concat_eq_append]; simp
    rw [D.pval_append]
    by_cases hz : Q.pend z v.reverse = x
    · rw [hz, hkill _ _ hvr, mul_zero, op_zero]
    · rw [hr, Pm, D.pval_cons_of_ne _ (by rw [hxc]; exact Ne.symm hz), zero_mul, mul_zero, op_zero]

variable (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
include hspan

/-- **The socle of `e_y A`** at the end of the longest path of a binomial vertex. -/
theorem socle_op {x : Q.V} (hb : Bin (k := k) hadm x) : ∃ y : Q.V,
    D.e y * zz (k := k) hadm x = zz (k := k) hadm x ∧
    ∀ t : A, D.e y * t = t → t ≠ 0 → ∃ c : A, t * c = zz (k := k) hadm x := by
  obtain ⟨a, b, hab, hxa, hxb, hmem, hz⟩ := zz_spec hadm hb
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
  set pa := D.pval x (Pm hadm a)
  set pb := D.pval x (Pm hadm b)
  have hpa := pval_Pm_ne hadm hsb hxa
  have hpb := pval_Pm_ne hadm hsb hxb
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_smul] at hμ; exact hpa hμ.symm
  have hpb' : pb = μ⁻¹ • pa := by rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hka : ∀ (w : Q.V) (σ : List Q.A), σ ≠ [] → pa * D.pval w σ = 0 := fun w σ hσ ↦ by
    have := zz_mul_path (k := k) hadm hsb x w hσ
    rwa [hz] at this
  have hkb : ∀ (w : Q.V) (σ : List Q.A), σ ≠ [] → pb * D.pval w σ = 0 := fun w σ hσ ↦ by
    rw [hpb', smul_mul_assoc, hka w σ hσ, smul_zero]
  set y := Q.pend x (Pm hadm a)
  have hya : D.e y * pa = pa := D.e_pend_mul_pval _ _
  have hyb : Q.pend x (Pm hadm b) = y := by
    by_contra hne
    apply hpb
    change pb = 0
    have h1 : D.e y * pb = pb := by rw [hpb', mul_smul_comm, hya]
    have h2 : D.e (Q.pend x (Pm hadm b)) * pb = pb := D.e_pend_mul_pval _ _
    rw [← h2, ← h1, ← mul_assoc, D.e_mul_e_of_ne hne, zero_mul]
  have hPa := Pm_op_eq hadm hsb hxa hka
  have hPb := Pm_op_eq hadm hsb hxb hkb
  set ar := (Pm hadm a).getLast (List.cons_ne_nil _ _)
  set bs := (Pm hadm b).getLast (List.cons_ne_nil _ _)
  have hya' : Q.op.src ar = y := by
    show Q.tgt ar = Q.pend x (a :: tl hadm a)
    conv_rhs => rw [← List.dropLast_append_getLast (List.cons_ne_nil a (tl hadm a))]
    rw [Q.pend_concat]
    rfl
  have hyb' : Q.op.src bs = y := by
    rw [← hyb]
    show Q.tgt bs = Q.pend x (b :: tl hadm b)
    conv_rhs => rw [← List.dropLast_append_getLast (List.cons_ne_nil b (tl hadm b))]
    rw [Q.pend_concat]
    rfl
  have hab' : ar ≠ bs := by
    intro h
    have : (Pm hadm a).reverse = (Pm hadm b).reverse := by rw [← hPa, ← hPb, h]
    have h2 := List.reverse_injective this
    simp only [Pm, List.cons.injEq] at h2
    exact hab h2.1
  have hva : D.opD.pval y (Pm (opD_adm hadm) ar) = op pa := by
    rw [hPa, ← D.op_pval hpa]
  have hvb : D.opD.pval y (Pm (opD_adm hadm) bs) = op pb := by
    rw [hPb, ← hyb, ← D.op_pval hpb]
  have hbop : Bin (k := k) (opD_adm hadm) y := ⟨ar, bs, hab', hya', hyb',
    Submodule.mem_span_singleton.mpr ⟨μ, by rw [hva, hvb, ← hμ]; rfl⟩⟩
  refine ⟨y, by rw [hz]; exact hya, fun t ht ht0 ↦ ?_⟩
  obtain ⟨c, hc⟩ := socle (opD_adm hadm) (opD_sb hsb) (opD_span hspan) hbop hya'
    (w := op t) (by show op t * op (D.e y) = op t; rw [← op_mul, ht])
    (by rw [Ne, op_eq_zero_iff]; exact ht0)
  refine ⟨c.unop, ?_⟩
  rw [hva] at hc
  apply op_injective
  rw [hz, ← hc, op_mul, op_unop]

end Socle

end PathData

end BrickAccessibility
