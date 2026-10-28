module

public import BrickAccessibility.StringQuotient.Opposite
public import BrickAccessibility.Quiver.Strings
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dual of a string module (equation (3.d))

Monomial data on `B` give monomial data on `Bᵐᵒᵖ` over the opposite quiver (`MonomialData.op`).
For a string `w`, the word `w^D` with the same letters and reversed directions is a string over
the opposite data (`Word.dualWord`, `Word.isString_dual`), and the `k`-dual of `M(w)`, a module
over `Bᵐᵒᵖ`, is isomorphic to `M(w^D)` (`Word.dualEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement MulOpposite

universe u

variable {k : Type*} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable (D : MonomialData k B)

theorem op_pval_ne {y : D.Q.V} {l : List D.Q.A} (h : D.toPathData.opD.pval y l ≠ 0) :
    D.pval (D.Q.op.pend y l) l.reverse ≠ 0 ∧
      D.toPathData.opD.pval y l = op (D.pval (D.Q.op.pend y l) l.reverse) := by
  rw [PathData.pval_op] at h ⊢
  have h1 : D.e y * D.pval (D.Q.op.pend y l) l.reverse ≠ 0 := fun h0 ↦ h (by rw [h0, op_zero])
  have h2 : D.pval (D.Q.op.pend y l) l.reverse ≠ 0 := fun h0 ↦ h1 (by rw [h0, mul_zero])
  refine ⟨h2, ?_⟩
  congr 1
  by_cases hy : y = D.Q.pend (D.Q.op.pend y l) l.reverse
  · have := D.toPathData.e_pend_mul_pval (D.Q.op.pend y l) l.reverse
    rw [← hy] at this
    exact this
  · exfalso; apply h1
    show D.toPathData.e y * D.toPathData.pval _ _ = 0
    rw [← D.toPathData.e_pend_mul_pval (D.Q.op.pend y l) l.reverse, ← mul_assoc,
      D.toPathData.e_mul_e_of_ne hy, zero_mul]

theorem op_pval_eq (y : D.Q.V) (l : List D.Q.A)
    (hy : y = D.Q.pend (D.Q.op.pend y l) l.reverse) :
    D.toPathData.opD.pval y l = op (D.pval (D.Q.op.pend y l) l.reverse) := by
  rw [PathData.pval_op]
  congr 1
  have := D.toPathData.e_pend_mul_pval (D.Q.op.pend y l) l.reverse
  rw [← hy] at this
  exact this

/-- **Monomial data of the opposite algebra.** -/
def op : MonomialData k Bᵐᵒᵖ where
  Q := D.Q.op
  toPathData := D.toPathData.opD
  span_pval := PathData.opD_span D.span_pval
  linIndep := by
    classical
    let g : {p : D.Q.op.V × List D.Q.op.A // D.toPathData.opD.pval p.1 p.2 ≠ 0} → D.NZPath :=
      fun p ↦ ⟨(D.Q.op.pend p.1.1 p.1.2, p.1.2.reverse), (D.op_pval_ne p.2).1⟩
    have hg : Function.Injective g := by
      rintro ⟨⟨y, l⟩, hp⟩ ⟨⟨y', l'⟩, hp'⟩ h
      simp only [g, Subtype.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hl : l = l' := List.reverse_injective h2
      subst hl
      have e1 := (D.op_pval_ne hp).2
      have e2 := (D.op_pval_ne hp').2
      rw [PathData.pval_op] at hp hp'
      -- the start vertex is determined by the end of the reversed path
      have hy : y = D.Q.pend (D.Q.op.pend y l) l.reverse := by
        by_contra hy
        apply hp
        rw [← D.toPathData.e_pend_mul_pval (D.Q.op.pend y l) l.reverse, ← mul_assoc,
          D.toPathData.e_mul_e_of_ne hy, zero_mul, op_zero]
      have hy' : y' = D.Q.pend (D.Q.op.pend y' l) l.reverse := by
        by_contra hy'
        apply hp'
        rw [← D.toPathData.e_pend_mul_pval (D.Q.op.pend y' l) l.reverse, ← mul_assoc,
          D.toPathData.e_mul_e_of_ne hy', zero_mul, op_zero]
      have : y = y' := by rw [hy, hy', h1]
      subst this
      rfl
    have hli := (D.linIndep.comp g hg).map' (MulOpposite.opLinearEquiv k).toLinearMap
      (LinearEquiv.ker _)
    have heq : (fun p : {p : D.Q.op.V × List D.Q.op.A // D.toPathData.opD.pval p.1 p.2 ≠ 0} ↦
        D.toPathData.opD.pval p.1.1 p.1.2) =
        (MulOpposite.opLinearEquiv k).toLinearMap ∘
          (fun q : D.NZPath ↦ D.toPathData.pval q.1.1 q.1.2) ∘ g := by
      funext p
      exact (D.op_pval_ne p.2).2
    rw [heq]
    exact hli
  e_ne v h := D.e_ne v (op_injective h)

end MonomialData

namespace MonomialData.CoeffQuiver

variable {D : MonomialData k B} (C : D.CoeffQuiver)

/-- Following a path ends over the end vertex of the path. -/
theorem follow_vtx : ∀ (l : List D.Q.A) (i : C.P) (q : C.P × k), C.follow i l = some q →
    C.vtx q.1 = D.Q.pend (C.vtx i) l := by
  intro l
  induction l with
  | nil => intro i q h; simp only [follow, Option.some.injEq] at h; subst h; rfl
  | cons a l ih =>
      intro i q h
      simp only [follow] at h
      cases hn : C.next a i with
      | none => rw [hn] at h; cases h
      | some j =>
          rw [hn] at h
          obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
          rw [ih j q' hq', C.next_tgt a i j hn]
          rfl

theorem follow_append : ∀ (l₁ l₂ : List D.Q.A) (i m n : C.P) (c d : k),
    C.follow i l₁ = some (m, c) → C.follow m l₂ = some (n, d) →
      C.follow i (l₁ ++ l₂) = some (n, c * d) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ i m n c d h1 h2
      simp only [follow, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simpa using h2
  | cons a l ih =>
      intro l₂ i m n c d h1 h2
      simp only [follow] at h1
      cases hn : C.next a i with
      | none => rw [hn] at h1; cases h1
      | some j =>
          rw [hn] at h1
          obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.mp h1
          simp only [Prod.mk.injEq] at hq'
          obtain ⟨rfl, rfl⟩ := hq'
          simp only [List.cons_append, follow, hn]
          rw [ih l₂ j q.1 n q.2 d (by rw [hq]) h2]
          simp [mul_assoc]

end MonomialData.CoeffQuiver

namespace Word

variable {D : MonomialData k B}

/-- The dual letter, over the opposite quiver. -/
def dualLetter (l : Letter D.Q) : Letter D.op.Q := (l.1, !l.2)

theorem dualLetter_src (l : Letter D.Q) : (dualLetter l).src = l.src := by
  obtain ⟨a, d⟩ := l
  cases d <;> rfl

theorem dualLetter_tgt (l : Letter D.Q) : (dualLetter l).tgt = l.tgt := by
  obtain ⟨a, d⟩ := l
  cases d <;> rfl

theorem isWalk_dual : ∀ (x : D.Q.V) (ls : List (Letter D.Q)), D.Q.IsWalk x ls →
    D.op.Q.IsWalk x (ls.map dualLetter) := by
  intro x ls
  induction ls generalizing x with
  | nil => intro _; trivial
  | cons l ls ih =>
      rintro ⟨h1, h2⟩
      exact ⟨by rw [dualLetter_src]; exact h1, by rw [dualLetter_tgt]; exact ih _ h2⟩

/-- **The dual word** `w^D`: the same letters with reversed directions, over `Q^op`. -/
def dualWord (w : Word D.Q) : Word D.op.Q where
  start := w.start
  letters := w.letters.map dualLetter
  walk := isWalk_dual _ _ w.walk

variable (w : Word D.Q)

theorem dualWord_len : (dualWord w).len = w.len := List.length_map _

theorem dualWord_letter (i : ℕ) (hi : i < (dualWord w).len) :
    (dualWord w).letters[i]'hi = dualLetter (w.letters[i]'(by rw [dualWord_len] at hi; exact hi)) :=
  List.getElem_map _

variable {w}

theorem next_iff {Q : FinQuiver} {v : Word Q} (hnf : v.NoForks) {a : Q.A}
    {i j : Fin (v.len + 1)} : v.next a i = some j ↔
      (∃ hi : i.val < v.letters.length, v.letters[i.val]'hi = (a, true) ∧ j.val = i.val + 1) ∨
      (∃ hi : 0 < i.val, v.letters[i.val - 1]'(by have := i.isLt; simp only [len] at this; omega)
        = (a, false) ∧ j.val = i.val - 1) := by
  refine ⟨v.next_eq_some, ?_⟩
  rintro (⟨hi, hl, hj⟩ | ⟨hi, hl, hj⟩)
  · unfold next
    rw [dif_pos ⟨hi, hl⟩]
    exact congrArg some (Fin.ext hj.symm)
  · unfold next
    have h1 : ¬ ∃ hi : i.val < v.letters.length, v.letters[i.val]'hi = (a, true) := by
      rintro ⟨hi', hl'⟩
      apply hnf (i.val - 1) (by omega)
      have e : i.val - 1 + 1 = i.val := by omega
      simp [e, hl, hl']
    rw [dif_neg h1, dif_pos ⟨hi, hl⟩]
    exact congrArg some (Fin.ext hj.symm)

theorem noForks_dual (hnf : w.NoForks) : (dualWord w).NoForks := by
  intro i hi h
  have hi' : i + 1 < w.letters.length := by
    have := dualWord_len w; simp only [len] at this; omega
  apply hnf i hi'
  rw [dualWord_letter w i (by simp only [len] at hi ⊢; omega),
    dualWord_letter w (i + 1) hi] at h
  simp only [dualLetter] at h
  exact ⟨h.1, fun h2 ↦ h.2 (by rw [h2])⟩

theorem dualLetter_eq_iff (x : Letter D.Q) (a : D.Q.A) (d : Bool) :
    dualLetter x = ((a, d) : Letter D.op.Q) ↔ x = (a, !d) := by
  obtain ⟨b, e⟩ := x
  cases d <;> cases e <;> simp [dualLetter, Prod.ext_iff] <;> rfl

/-- **The moves of `w^D` reverse the moves of `w`.** -/
theorem dual_next_iff (hnf : w.NoForks) {a : D.Q.A} (i j : Fin ((dualWord w).len + 1)) :
    (dualWord w).next a i = some j ↔
      w.next a ⟨j.val, by have := j.isLt; have := dualWord_len w; omega⟩ =
        some ⟨i.val, by have := i.isLt; have := dualWord_len w; omega⟩ := by
  have hlen := dualWord_len w
  have hi0 := i.isLt
  have hj0 := j.isLt
  simp only [len] at hlen hi0 hj0
  have hl : ∀ (m : ℕ) (hm : m < (dualWord w).letters.length) (d : Bool),
      (dualWord w).letters[m]'hm = (a, d) ↔ w.letters[m]'(by omega) = (a, !d) := fun m hm d ↦ by
    rw [dualWord_letter w m hm]
    exact dualLetter_eq_iff _ a d
  erw [next_iff (noForks_dual hnf), next_iff hnf]
  constructor
  · rintro (⟨hi, h, hj⟩ | ⟨hi, h, hj⟩)
    · right
      have h' := (hl _ hi true).mp h
      refine ⟨by simp only; omega, ?_, by simp only; omega⟩
      have e : j.val - 1 = i.val := by omega
      simp only [e]
      simpa using h'
    · left
      have hm : i.val - 1 < (dualWord w).letters.length := by omega
      have h' := (hl _ hm false).mp h
      refine ⟨by simp only; omega, ?_, by simp only; omega⟩
      have e : j.val = i.val - 1 := by omega
      simp only [e]
      simpa using h'
  · rintro (⟨hjl, h, hj⟩ | ⟨hjp, h, hj⟩)
    · right
      simp only at hjl h hj
      refine ⟨by omega, (hl _ (by omega) false).mpr ?_, by omega⟩
      have e : i.val - 1 = j.val := by omega
      simp only [e]
      simpa using h
    · left
      simp only at hjp h hj
      refine ⟨by omega, (hl _ (by omega) true).mpr ?_, by omega⟩
      have e : i.val = j.val - 1 := by omega
      simp only [e]
      simpa using h

theorem wend_dual : ∀ (x : D.Q.V) (ls : List (Letter D.Q)),
    D.op.Q.wend x (ls.map dualLetter) = D.Q.wend x ls := by
  intro x ls
  induction ls generalizing x with
  | nil => rfl
  | cons l ls ih => exact (ih _).trans (by rw [dualLetter_tgt]; rfl)

theorem dual_vtx (p : Fin ((dualWord w).len + 1)) :
    (dualWord w).vtx p = w.vtx ⟨p.val, by have := p.isLt; have := dualWord_len w; omega⟩ := by
  show D.op.Q.wend w.start ((w.letters.map dualLetter).take p.val) =
    D.Q.wend w.start (w.letters.take p.val)
  rw [← List.map_take, wend_dual]

/-- Walks along `w^D` are reversed walks along `w`. -/
theorem dual_follow (hnf : w.NoForks) : ∀ (l : List D.Q.A) (i : Fin ((dualWord w).len + 1))
    (q : Fin ((dualWord w).len + 1) × k),
    ((dualWord w).coeffQuiver D.op).follow i l = some q →
      ∃ c : k, (w.coeffQuiver D).follow ⟨q.1.val, by have := q.1.isLt; have := dualWord_len w; omega⟩
        l.reverse = some (⟨i.val, by have := i.isLt; have := dualWord_len w; omega⟩, c) := by
  intro l
  induction l with
  | nil =>
      intro i q h
      have h' : some (i, (1 : k)) = some q := h
      obtain rfl := Option.some.inj h'
      exact ⟨1, rfl⟩
  | cons a l ih =>
      intro i q h
      simp only [MonomialData.CoeffQuiver.follow] at h
      cases hn : ((dualWord w).coeffQuiver D.op).next a i with
      | none => rw [hn] at h; cases h
      | some i₁ =>
          rw [hn] at h
          obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨c, hc⟩ := ih i₁ q' hq'
          have hnext := (dual_next_iff hnf i i₁).mp hn
          have hstep : (w.coeffQuiver D).follow
              ⟨i₁.val, by have := i₁.isLt; have := dualWord_len w; omega⟩ [a] =
              some (⟨i.val, by have := i.isLt; have := dualWord_len w; omega⟩, 1) := by
            have hn2 : (w.coeffQuiver D).next a
                ⟨i₁.val, by have := i₁.isLt; have := dualWord_len w; omega⟩ =
                some ⟨i.val, by have := i.isLt; have := dualWord_len w; omega⟩ := hnext
            simp only [MonomialData.CoeffQuiver.follow]
            rw [hn2]
            simp [Word.coeffQuiver]
          refine ⟨c * 1, ?_⟩
          simp only [List.reverse_cons]
          exact MonomialData.CoeffQuiver.follow_append _ _ _ _ _ _ _ _ hc hstep

/-- **The dual word of a string is a string** over the opposite data. -/
theorem isString_dual (hw : w.IsString D) : (dualWord w).IsString D.op := by
  refine ⟨noForks_dual hw.1, fun y l hz i hi ↦ ?_⟩
  by_contra hne
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨c, hc⟩ := dual_follow hw.1 l i q hq
  have hv1 : (dualWord w).vtx q.1 = D.Q.op.pend ((dualWord w).vtx i) l :=
    MonomialData.CoeffQuiver.follow_vtx ((dualWord w).coeffQuiver D.op) l i q hq
  have hv2 : w.vtx ⟨i.val, by have := i.isLt; have := dualWord_len w; omega⟩ =
      D.Q.pend (w.vtx ⟨q.1.val, by have := q.1.isLt; have := dualWord_len w; omega⟩) l.reverse :=
    MonomialData.CoeffQuiver.follow_vtx (w.coeffQuiver D) l.reverse _ _ hc
  have hi' : (dualWord w).vtx i = y := hi
  have e1 : w.vtx ⟨q.1.val, by have := q.1.isLt; have := dualWord_len w; omega⟩ =
      D.Q.op.pend y l := (dual_vtx (w := w) q.1).symm.trans (by rw [hv1, hi'])
  have e2 : y = D.Q.pend (D.Q.op.pend y l) l.reverse :=
    ((dual_vtx (w := w) i).symm.trans hi').symm.trans (hv2.trans (by rw [e1]))
  have hnz : D.pval (D.Q.op.pend y l) l.reverse ≠ 0 := by
    intro h0
    have := hw.2 _ l.reverse h0 _ e1
    exact Option.some_ne_none _ (hc.symm.trans this)
  exact hnz (op_injective (((D.op_pval_eq y l e2).symm.trans hz).trans op_zero.symm))

end Word

/-! ### The `k`-dual as a module over the opposite algebra -/

section KDual

variable (k B) (M : Type*) [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]

/-- The `k`-dual `DM` of a left `B`-module `M`, a left `Bᵐᵒᵖ`-module by
`(op b • f) m = f (b • m)`. -/
@[nolint unusedArguments]
def KDual (k : Type*) [Field k] (_B : Type*) (M : Type*) [AddCommGroup M] [Module k M] :
    Type _ :=
  Module.Dual k M

instance : AddCommGroup (KDual k B M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance : Module k (KDual k B M) := inferInstanceAs (Module k (Module.Dual k M))
instance [FiniteDimensional k M] : FiniteDimensional k (KDual k B M) :=
  inferInstanceAs (FiniteDimensional k (Module.Dual k M))

variable {k B M}

/-- The underlying functional. -/
def KDual.toDual : KDual k B M ≃ₗ[k] Module.Dual k M := LinearEquiv.refl k _

/-- The action of `b` on `M` as a `k`-linear map. -/
def actK (b : B) : M →ₗ[k] M where
  toFun m := b • m
  map_add' := smul_add b
  map_smul' c m := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul (A := B) c m, ← algebraMap_smul (A := B) c (b • m), smul_smul,
      smul_smul, Algebra.commutes]

instance : SMul Bᵐᵒᵖ (KDual k B M) where
  smul b f := KDual.toDual.symm (KDual.toDual f ∘ₗ actK b.unop)

theorem KDual.smul_apply (b : Bᵐᵒᵖ) (f : KDual k B M) (m : M) :
    KDual.toDual (b • f) m = KDual.toDual f (b.unop • m) := rfl

omit [Ring B] [Algebra k B] [Module B M] [IsScalarTower k B M] in
theorem KDual.ext {f g : KDual k B M} (h : ∀ m, KDual.toDual f m = KDual.toDual g m) : f = g :=
  KDual.toDual.injective (LinearMap.ext h)

instance : Module Bᵐᵒᵖ (KDual k B M) where
  one_smul f := KDual.ext fun m ↦ by rw [KDual.smul_apply, unop_one, one_smul]
  mul_smul b c f := KDual.ext fun m ↦ by
    rw [KDual.smul_apply, KDual.smul_apply, KDual.smul_apply, unop_mul, mul_smul]
  smul_zero b := KDual.ext fun m ↦ by rw [KDual.smul_apply]; rfl
  smul_add b f g := KDual.ext fun m ↦ by
    rw [KDual.smul_apply, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      KDual.smul_apply, KDual.smul_apply]
  add_smul b c f := KDual.ext fun m ↦ by
    rw [KDual.smul_apply, map_add, LinearMap.add_apply, KDual.smul_apply, KDual.smul_apply,
      unop_add, add_smul, map_add]
  zero_smul f := KDual.ext fun m ↦ by
    rw [KDual.smul_apply, unop_zero, zero_smul, map_zero, map_zero]; rfl

instance : IsScalarTower k Bᵐᵒᵖ (KDual k B M) where
  smul_assoc c b f := KDual.ext fun m ↦ by
    rw [KDual.smul_apply, unop_smul, smul_assoc, (KDual.toDual f).map_smul,
      LinearEquiv.map_smul, LinearMap.smul_apply, KDual.smul_apply]

end KDual

/-! ### The isomorphism `DM(w) ≅ M(w^D)` -/

namespace Word

open MonomialData

variable {D : MonomialData k B} {w : Word D.Q} (hw : w.IsString D)

/-- Positions of `w^D` are the positions of `w`. -/
def posEquiv (w : Word D.Q) : Fin ((dualWord w).len + 1) ≃ Fin (w.len + 1) :=
  finCongr (by rw [dualWord_len])

/-- The basis vector `z_i` of `M(w)`. -/
def zb (i : Fin (w.len + 1)) : w.stringModule D hw :=
  (((w.coeffQuiver D).toRep hw.2).equivV).symm (Pi.single i 1)

/-- The dual-basis map `DM(w) → M(w^D)`, `f ↦ ∑ f(z_j) z_j^D`. -/
def dualMapK : KDual k B (w.stringModule D hw) →ₗ[k]
    (dualWord w).stringModule D.op (isString_dual hw) where
  toFun f := ((((dualWord w).coeffQuiver D.op).toRep (isString_dual hw).2).equivV).symm
    fun j ↦ KDual.toDual f (zb hw (posEquiv w j))
  map_add' f g := by rw [← map_add]; congr 1
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; congr 1

theorem dualMapK_apply (f : KDual k B (w.stringModule D hw)) (j : Fin ((dualWord w).len + 1)) :
    (((dualWord w).coeffQuiver D.op).toRep (isString_dual hw).2).equivV (dualMapK hw f) j =
      KDual.toDual f (zb hw (posEquiv w j)) := rfl

theorem dualMapK_e (v : D.op.Q.V) (f : KDual k B (w.stringModule D hw)) :
    dualMapK hw (D.op.e v • f) = D.op.e v • dualMapK hw f := by
  rw [Rep.e_smul]
  apply (((dualWord w).coeffQuiver D.op).toRep (isString_dual hw).2).equivV.injective
  refine funext fun (j : Fin ((dualWord w).len + 1)) ↦ ?_
  change KDual.toDual f (D.e v • zb hw (posEquiv w j)) =
    if (dualWord w).vtx j = v then KDual.toDual f (zb hw (posEquiv w j)) else 0
  have key := Rep.e_smul ((w.coeffQuiver D).toRep hw.2) v (zb hw (posEquiv w j))
  rw [key]
  change KDual.toDual f ((w.coeffQuiver D).eMap v (Pi.single (posEquiv w j) 1)) = _
  have h1 := (w.coeffQuiver D).eMap_single v (posEquiv w j) 1
  rw [h1, dual_vtx]
  split_ifs with ha hb hb
  · rfl
  · exact absurd ha hb
  · exact absurd hb ha
  · exact map_zero _

theorem dualMapK_α (a : D.op.Q.A) (f : KDual k B (w.stringModule D hw)) :
    dualMapK hw (D.op.α a • f) = D.op.α a • dualMapK hw f := by
  rw [Rep.α_smul]
  apply (((dualWord w).coeffQuiver D.op).toRep (isString_dual hw).2).equivV.injective
  refine funext fun (j : Fin ((dualWord w).len + 1)) ↦ ?_
  change KDual.toDual f (D.α a • zb hw (posEquiv w j)) =
    ∑ i, if (dualWord w).next a i = some j then 1 * KDual.toDual f (zb hw (posEquiv w i)) else 0
  have key := Rep.α_smul ((w.coeffQuiver D).toRep hw.2) a (zb hw (posEquiv w j))
  rw [key]
  change KDual.toDual f ((w.coeffQuiver D).αMap a (Pi.single (posEquiv w j) 1)) = _
  have h1 := (w.coeffQuiver D).αMap_single a (posEquiv w j) 1
  rw [h1]
  have hiff : ∀ i, (dualWord w).next a i = some j ↔ w.next a (posEquiv w j) = some (posEquiv w i) :=
    fun i ↦ dual_next_iff hw.1 i j
  cases hn : (w.coeffQuiver D).next a (posEquiv w j) with
  | none =>
      refine (map_zero _).trans (Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ ?_).symm
      exact Option.some_ne_none _ (hn.symm.trans ((hiff i).mp h)).symm
  | some j' =>
      rw [Finset.sum_eq_single ((posEquiv w).symm j')]
      · rw [if_pos ?hc]
        · have e1 : posEquiv w ((posEquiv w).symm j') = j' := Equiv.apply_symm_apply _ j'
          show KDual.toDual f (Pi.single j' ((1 : k) * 1)) =
            1 * KDual.toDual f (zb hw (posEquiv w ((posEquiv w).symm j')))
          rw [e1, one_mul, one_mul]
          rfl
        · exact (hiff _).mpr (hn.trans (congrArg some (Equiv.apply_symm_apply _ j').symm))
      · intro i _ hi
        refine if_neg fun h ↦ hi ?_
        exact ((Equiv.symm_apply_eq _).mpr
          (Option.some.inj (hn.symm.trans ((hiff i).mp h)))).symm
      · simp

/-- **Equation (3.d):** `DM(w) ≅ M(w^D)` as modules over the opposite algebra. -/
def dualEquiv : KDual k B (w.stringModule D hw) ≃ₗ[Bᵐᵒᵖ]
    (dualWord w).stringModule D.op (isString_dual hw) := by
  refine LinearEquiv.ofBijective (D.op.linearMap_of_commute (dualMapK hw) (dualMapK_e hw)
    (dualMapK_α hw)) ?_
  have hinj : Function.Injective (dualMapK hw) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply KDual.toDual.injective
    rw [map_zero]
    have h0 : ∀ i, KDual.toDual f (zb hw i) = 0 := fun i ↦ by
      have := congrFun (congrArg (((dualWord w).coeffQuiver D.op).toRep
        (isString_dual hw).2).equivV hf) ((posEquiv w).symm i)
      rw [dualMapK_apply, Equiv.apply_symm_apply, map_zero] at this
      exact this
    have hg : KDual.toDual f ∘ₗ (((w.coeffQuiver D).toRep hw.2).equivV).symm.toLinearMap = 0 := by
      refine LinearMap.pi_ext fun i c ↦ ?_
      rw [LinearMap.zero_apply, LinearMap.comp_apply, show (Pi.single i c : _ → k) =
        c • Pi.single i 1 by ext x; simp [Pi.single_apply]]
      rw [LinearEquiv.coe_toLinearMap, map_smul, map_smul]
      change c • KDual.toDual f (zb hw i) = 0
      exact (congrArg (c • ·) (h0 i)).trans (smul_zero c)
    refine LinearMap.ext fun m ↦ ?_
    have := LinearMap.congr_fun hg (((w.coeffQuiver D).toRep hw.2).equivV m)
    simpa using this
  have hdim : Module.finrank k (KDual k B (w.stringModule D hw)) =
      Module.finrank k ((dualWord w).stringModule D.op (isString_dual hw)) := by
    rw [KDual.toDual.finrank_eq, Subspace.dual_finrank_eq,
      (((w.coeffQuiver D).toRep hw.2).equivV).finrank_eq,
      ((((dualWord w).coeffQuiver D.op).toRep (isString_dual hw).2).equivV).finrank_eq]
    change Module.finrank k (Fin (w.len + 1) → k) = Module.finrank k (Fin ((dualWord w).len + 1) → k)
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun, dualWord_len]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end Word

end BrickAccessibility
