module

public import BrickAccessibility.SkowWasch.Biserial

/-!
# Basic data of the opposite algebra

Basic data for `Cᵐᵒᵖ` give basic data for `C` (`unopB`), with corners, arrows and the
chain condition corresponding under `op` (`mem_Mk_unopB`, `arr_unopB`, `chainX_unopB`).
Left chains in `C` are right chains in `Cᵐᵒᵖ` (`rchain_of_lchain`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

namespace BasicData

open MulOpposite

universe u

variable {k : Type*} [Field k] {C : Type u} [Ring C] [Algebra k C] (B : BasicData k Cᵐᵒᵖ)

/-- The basic data of `C` obtained from those of `Cᵐᵒᵖ`. -/
def unopB : BasicData k C where
  n := B.n
  e v := (B.e v).unop
  e_mul_e v w := by
    apply op_injective
    rw [op_mul, op_unop, op_unop, B.e_mul_e]
    by_cases h : v = w
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, op_zero]
  sum_e := by
    apply op_injective
    rw [show op (∑ v, (B.e v).unop) = ∑ v, op (B.e v).unop from
      map_sum MulOpposite.opAddEquiv _ _]
    simp only [op_unop, B.sum_e, op_one]
  R := B.R.comap (MulOpposite.opLinearEquiv k : C ≃ₗ[k] Cᵐᵒᵖ).toLinearMap
  mul_mem_left a r hr := by
    show op (a * r) ∈ B.R
    rw [op_mul]; exact B.mul_mem_right _ _ hr
  mul_mem_right r a hr := by
    show op (r * a) ∈ B.R
    rw [op_mul]; exact B.mul_mem_left _ _ hr
  pow_eq_bot := by
    set R' := B.R.comap (MulOpposite.opLinearEquiv k : C ≃ₗ[k] Cᵐᵒᵖ).toLinearMap
    have key : ∀ m : ℕ, ∀ x ∈ R' ^ (m + 1), op x ∈ B.R ^ (m + 1) := by
      intro m
      induction m with
      | zero => intro x hx; rw [pow_one] at hx ⊢; exact hx
      | succ m ih =>
          intro x hx
          rw [pow_succ] at hx
          refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
          · rw [op_mul, pow_succ']
            exact Submodule.mul_mem_mul hb (ih a ha)
          · rw [op_add]; exact Submodule.add_mem _ ha hb
    obtain ⟨N, hN⟩ := B.pow_eq_bot
    refine ⟨N + 1, eq_bot_iff.mpr fun x hx ↦ ?_⟩
    have h1 := key N x hx
    have hN' : B.R ^ (N + 1) = ⊥ := by rw [pow_succ, hN, Submodule.bot_mul]
    rw [hN'] at h1
    exact (Submodule.mem_bot k).mpr (op_injective ((Submodule.mem_bot k).mp h1))
  decomp a := by
    obtain ⟨c, hc⟩ := B.decomp (op a)
    refine ⟨c, ?_⟩
    show op (a - ∑ v, c v • (B.e v).unop) ∈ B.R
    rw [op_sub, show op (∑ v, c v • (B.e v).unop) = ∑ v, op (c v • (B.e v).unop) from
      map_sum MulOpposite.opAddEquiv _ _]
    simpa [op_smul] using hc
  e_not_mem v h := B.e_not_mem v (by simpa using h)

theorem mem_R_unopB {x : C} : x ∈ B.unopB.R ↔ op x ∈ B.R := Iff.rfl

theorem e_unopB (v : Fin B.n) : B.unopB.e v = (B.e v).unop := rfl

theorem mem_Mk_unopB {i j : Fin B.n} {y : C} : y ∈ B.unopB.Mk i j ↔ op y ∈ B.Mk j i := by
  show (B.unopB.e j * y * B.unopB.e i = y ∧ y ∈ B.unopB.R) ↔
    (B.e i * op y * B.e j = op y ∧ op y ∈ B.R)
  rw [mem_R_unopB, e_unopB, e_unopB]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    have := congrArg op h
    rw [op_mul, op_mul, op_unop, op_unop] at this
    rw [mul_assoc]; exact this
  · rintro ⟨h, h'⟩
    refine ⟨op_injective ?_, h'⟩
    rw [op_mul, op_mul, op_unop, op_unop, ← mul_assoc, h]

theorem mem_sq_unopB {y : C} : y ∈ B.unopB.R * B.unopB.R ↔ op y ∈ B.R * B.R := by
  constructor
  · intro hy
    refine Submodule.mul_induction_on hy (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [op_mul]; exact Submodule.mul_mem_mul hb ha
    · rw [op_add]; exact Submodule.add_mem _ ha hb
  · intro hy
    have : ∀ w ∈ B.R * B.R, w.unop ∈ B.unopB.R * B.unopB.R := by
      intro w hw
      refine Submodule.mul_induction_on hw (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
      · rw [unop_mul]
        exact Submodule.mul_mem_mul (show op b.unop ∈ B.R by simpa using hb)
          (show op a.unop ∈ B.R by simpa using ha)
      · rw [unop_add]; exact Submodule.add_mem _ ha hb
    simpa using this _ hy

theorem arr_unopB {i j : Fin B.n} : B.unopB.Arr i j ↔ B.Arr j i := by
  constructor
  · rintro ⟨g, hg, hg2⟩
    exact ⟨op g, B.mem_Mk_unopB.mp hg, fun h ↦ hg2 (B.mem_sq_unopB.mpr h)⟩
  · rintro ⟨g, hg, hg2⟩
    refine ⟨g.unop, B.mem_Mk_unopB.mpr (by simpa using hg), fun h ↦ hg2 ?_⟩
    simpa using B.mem_sq_unopB.mp h

theorem unop_mem_Id {z : Cᵐᵒᵖ} {w : Cᵐᵒᵖ} (hw : w ∈ Id (k := k) z) :
    w.unop ∈ Id (k := k) z.unop := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, b, rfl⟩ := hw
      exact Submodule.subset_span ⟨b.unop, a.unop, by simp [mul_assoc]⟩
  | zero => simp
  | add w w' _ _ h h' => rw [unop_add]; exact Submodule.add_mem _ h h'
  | smul c w _ h => rw [unop_smul]; exact Submodule.smul_mem _ c h

theorem chainX_unopB (hX : B.ChainX) : B.unopB.ChainX := by
  intro i j z z' hz hz'
  have h1 : B.e j * op z * B.e i = op z := by
    have := congrArg op hz
    rw [op_mul, op_mul] at this
    change op ((B.e j).unop) * (op z * op ((B.e i).unop)) = op z at this
    rw [op_unop, op_unop] at this
    rw [mul_assoc]; exact this
  have h2 : B.e j * op z' * B.e i = op z' := by
    have := congrArg op hz'
    rw [op_mul, op_mul] at this
    change op ((B.e j).unop) * (op z' * op ((B.e i).unop)) = op z' at this
    rw [op_unop, op_unop] at this
    rw [mul_assoc]; exact this
  rcases hX j i (op z) (op z') h1 h2 with h | h
  · left; simpa using unop_mem_Id h
  · right; simpa using unop_mem_Id h

/-- Left chains in `C` are right chains in `Cᵐᵒᵖ`. -/
theorem rchain_of_lchain {a : Cᵐᵒᵖ} (h : LChain a.unop) : RChain a := by
  intro u v
  rcases h u.unop v.unop with ⟨w, hw⟩ | ⟨w, hw⟩
  · left; refine ⟨op w, ?_⟩
    have := congrArg op hw
    simpa [mul_assoc] using this
  · right; refine ⟨op w, ?_⟩
    have := congrArg op hw
    simpa [mul_assoc] using this

end BasicData

end SkowWasch

end BrickAccessibility
