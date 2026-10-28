module

public import BrickAccessibility.Section4.ExtBoundDual

/-!
# Exact dimensions of `Ext¹(M, S_v)` and `Ext¹(S_v, M)`

For quadratic monomial data the bounds of `finrank_ext1_simple_le` and
`finrank_ext1_simple_left_le` are equalities:

* every admissible family `(ψ_b)` comes from a normalized derivation, defined on a path
  `p b` (last arrow `b`) by `δ(p b)(m) = ψ_b(p m)` (`δR`, `δR_mem_cocycles`), and dually on
  a path `b p` (first arrow `b`) by `δ(b p)(s) = p χ_b` (`δL`, `δL_mem_cocycles`);
* the inner derivations among the normalized ones are exactly those of functionals
  supported at `v`, with kernel `K₀`.

Hence `dim Ext¹(M, S_v) + dim E₀ = Σ_b dim Z_b + dim K₀` (`finrank_ext1_simple_eq`) and
`dim Ext¹(S_v, M) + dim E₀' = Σ_b dim Y_b + dim K₀'` (`finrank_ext1_simple_left_eq`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable (D : MonomialData k B)

section Paths

theorem isWalk_of_pval_ne_zero : ∀ (x : D.Q.V) (l : List D.Q.A), D.pval x l ≠ 0 →
    D.Q.IsWalk x (l.map (·, true))
  | _, [], _ => trivial
  | x, a :: l, h => by
      have hsrc : D.Q.src a = x := by
        by_contra hne; exact h (D.toPathData.pval_cons_of_ne l hne)
      have hl : D.pval (D.Q.tgt a) l ≠ 0 := fun h0 ↦ h (by
        show D.toPathData.pval (D.Q.tgt a) l * D.α a * D.e x = 0
        rw [show D.toPathData.pval (D.Q.tgt a) l = 0 from h0, zero_mul, zero_mul])
      exact ⟨by simp [Letter.src, hsrc], isWalk_of_pval_ne_zero (D.Q.tgt a) l hl⟩

theorem pend_concat : ∀ (x : D.Q.V) (l : List D.Q.A) (b : D.Q.A),
    D.Q.pend x (l ++ [b]) = D.Q.tgt b
  | _, [], _ => rfl
  | _, a :: l, b => pend_concat (D.Q.tgt a) l b

theorem isWalk_concat : ∀ (x : D.Q.V) (l : List D.Q.A) (b : D.Q.A),
    D.Q.IsWalk x (l.map (·, true)) → D.Q.pend x l = D.Q.src b →
      D.Q.IsWalk x ((l ++ [b]).map (·, true))
  | x, [], b, _, h => ⟨by simp [Letter.src, ← h, Statement.FinQuiver.pend], trivial⟩
  | x, a :: l, b, hw, h => ⟨hw.1, isWalk_concat _ l b hw.2 h⟩

theorem eq_nil_or_snoc {α : Type*} (l : List α) : l = [] ∨ ∃ l' b, l = l' ++ [b] := by
  rcases List.eq_nil_or_concat l with h | ⟨l', b, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨l', b, by rw [h, List.concat_eq_append]⟩

theorem pval_concat (x : D.Q.V) (l : List D.Q.A) (b : D.Q.A) :
    D.pval x (l ++ [b]) = D.α b * D.pval x l := by
  show D.toPathData.pval x (l ++ [b]) = D.α b * D.toPathData.pval x l
  rw [D.toPathData.pval_append, D.toPathData.pval_single, mul_assoc,
    D.toPathData.e_pend_mul_pval]

theorem pval_append' (x : D.Q.V) (l₁ l₂ : List D.Q.A) :
    D.pval x (l₁ ++ l₂) = D.pval (D.Q.pend x l₁) l₂ * D.pval x l₁ :=
  D.toPathData.pval_append x l₁ l₂

theorem α_ne_zero (hq : D.IsQuadratic) (a : D.Q.A) : D.α a ≠ 0 := by
  intro h
  have h1 : D.pval (D.Q.src a) [a] = 0 := by
    show D.toPathData.pval (D.Q.src a) [a] = 0
    rw [D.toPathData.pval_single_src]; exact h
  obtain ⟨i, hi, -⟩ := (hq a [] (by simp [Statement.FinQuiver.IsWalk, Letter.src])).mp h1
  simp at hi

theorem pval_mul_pval (x x' : D.Q.V) (l l' : List D.Q.A) :
    D.pval x' l' * D.pval x l = if D.Q.pend x l = x' then D.pval x (l ++ l') else 0 := by
  show D.toPathData.pval x' l' * D.toPathData.pval x l =
    if D.Q.pend x l = x' then D.toPathData.pval x (l ++ l') else 0
  split_ifs with h
  · rw [D.toPathData.pval_append, h]
  · rw [← D.toPathData.pval_mul_e x' l', ← D.toPathData.e_pend_mul_pval x l, mul_assoc,
      ← mul_assoc (D.e x'), D.toPathData.e_mul_e_of_ne (Ne.symm h), zero_mul, mul_zero]

/-- In quadratic monomial data, a nonzero path followed by a composable arrow is zero only
through a relation at the junction. -/
theorem forbidden_of_concat (hq : D.IsQuadratic) {x : D.Q.V} {l : List D.Q.A} {b : D.Q.A}
    (h0 : D.pval x l ≠ 0) (hz : D.pval x (l ++ [b]) = 0) (hpe : D.Q.pend x l = D.Q.src b) :
    ∃ hl : l ≠ [], D.toPathData.Forbidden (l.getLast hl) b := by
  rcases l with _ | ⟨a, r⟩
  · exfalso
    have hx : x = D.Q.src b := hpe
    subst hx
    have := (hq b [] (by simp [Statement.FinQuiver.IsWalk, Letter.src])).mp
      (by simpa using hz)
    obtain ⟨i, hi, -⟩ := this
    simp at hi
  · have hw := D.isWalk_of_pval_ne_zero x (a :: r) h0
    have hx : D.Q.src a = x := by simpa [Letter.src] using hw.1
    subst hx
    have hwalk := D.isWalk_concat _ (a :: r) b hw hpe
    obtain ⟨i, hi, hf⟩ := (hq a (r ++ [b]) (by simpa using hwalk)).mp (by simpa using hz)
    have hlen : (a :: (r ++ [b])).length = r.length + 2 := by simp
    have key : ∀ j (hj : j < r.length + 1),
        (a :: (r ++ [b]))[j]'(by simp; omega) = (a :: r)[j]'(by simpa using hj) := by
      intro j hj
      rcases j with _ | j
      · rfl
      · simp [List.getElem_append_left (show j < r.length by omega)]
    by_cases hin : i + 1 < r.length + 1
    · exfalso
      apply h0
      refine (hq a r (by simpa using hw)).mpr ⟨i, by simpa using hin, ?_⟩
      rw [key i (by omega), key (i + 1) hin] at hf
      exact hf
    · have hi' : i = r.length := by rw [hlen] at hi; omega
      subst hi'
      refine ⟨List.cons_ne_nil a r, ?_⟩
      have e1 : (a :: (r ++ [b]))[r.length]'(by omega) = (a :: r).getLast (List.cons_ne_nil a r) := by
        rw [key r.length (by omega), List.getLast_eq_getElem]
        simp
      have e2 : (a :: (r ++ [b]))[r.length + 1]'hi = b := by simp
      rw [e1, e2] at hf
      exact hf

end Paths

variable {M : Type u} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- Left multiplication on a module, as a `k`-linear map. -/
def lsm (c : B) : M →ₗ[k] M where
  toFun m := c • m
  map_add' := smul_add c
  map_smul' a m := by rw [RingHom.id_apply, smul_comm]

theorem lsm_apply (c : B) (m : M) : (lsm c : M →ₗ[k] M) m = c • m := rfl

theorem pval_smul_simple (v x : D.Q.V) {l : List D.Q.A} (hl : l ≠ []) (s : D.simple v) :
    D.pval x l • s = 0 := by
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hl
  show (D.toPathData.pval (D.Q.tgt a) r * D.α a * D.e x) • s = 0
  rw [mul_smul, mul_smul, D.α_smul_simple, smul_zero]

/-! ### Derivations into `Hom_k(M, S_v)` -/

section Right

variable (v : D.Q.V) (ψ : D.Q.A → M →ₗ[k] D.simple v)

/-- The value of the derivation on a path `p b` with last arrow `b`: `ψ_b ∘ p`. -/
def dR (x : D.Q.V) (l : List D.Q.A) : M →ₗ[k] D.simple v :=
  match l.getLast? with
  | none => 0
  | some b => ψ b ∘ₗ lsm (D.pval x l.dropLast)

theorem dR_nil (x : D.Q.V) : D.dR v ψ x [] = 0 := rfl

theorem dR_concat (x : D.Q.V) (l : List D.Q.A) (b : D.Q.A) :
    D.dR v ψ x (l ++ [b]) = ψ b ∘ₗ lsm (D.pval x l) := by
  simp [dR]

/-- The derivation, extended linearly from the path basis. -/
def δR : B →ₗ[k] M →ₗ[k] D.simple v :=
  D.basis.constr k fun p ↦ D.dR v ψ p.1.1 p.1.2

variable {v ψ} (hψv : ∀ b, D.Q.tgt b ≠ v → ψ b = 0)
  (hψe : ∀ b m, ψ b (D.e (D.Q.src b) • m) = ψ b m)
  (hψf : ∀ a b, D.toPathData.Forbidden a b → ∀ m, ψ b (D.α a • m) = 0)

include hψe hψf in
theorem dR_eq_zero (hq : D.IsQuadratic) {x : D.Q.V} {l : List D.Q.A} (h : D.pval x l = 0) :
    D.dR v ψ x l = 0 := by
  rcases eq_nil_or_snoc l with rfl | ⟨l', b, rfl⟩
  · exact absurd h (D.e_ne x)
  rw [dR_concat]
  refine LinearMap.ext fun m ↦ ?_
  rw [LinearMap.comp_apply, lsm_apply, LinearMap.zero_apply]
  by_cases h0 : D.pval x l' = 0
  · rw [h0, zero_smul, map_zero]
  by_cases hpe : D.Q.pend x l' = D.Q.src b
  · obtain ⟨hl, hf⟩ := D.forbidden_of_concat hq h0 h hpe
    obtain ⟨l'', a, rfl⟩ := (eq_nil_or_snoc l').resolve_left hl
    rw [D.pval_concat, mul_smul]
    simp only [List.getLast_concat] at hf
    exact hψf a b hf _
  · rw [← hψe, ← mul_smul, show D.pval x l' = D.e (D.Q.pend x l') * D.pval x l' from
      (D.toPathData.e_pend_mul_pval x l').symm, ← mul_assoc,
      D.toPathData.e_mul_e_of_ne (Ne.symm hpe), zero_mul, zero_smul, map_zero]

include hψe hψf in
theorem δR_pval (hq : D.IsQuadratic) (x : D.Q.V) (l : List D.Q.A) :
    D.δR v ψ (D.pval x l) = D.dR v ψ x l := by
  by_cases h : D.pval x l = 0
  · rw [h, map_zero, D.dR_eq_zero hψe hψf hq h]
  · have : D.pval x l = D.basis ⟨(x, l), h⟩ := (D.basis_apply ⟨(x, l), h⟩).symm
    rw [this, δR, Basis.constr_basis]

include hψv hψe hψf in
/-- **The derivation rule on pairs of paths.** -/
theorem δR_leibniz_pval (hq : D.IsQuadratic) (x x' : D.Q.V) (l l' : List D.Q.A) (m : M) :
    D.δR v ψ (D.pval x' l' * D.pval x l) m =
      D.pval x' l' • D.δR v ψ (D.pval x l) m +
        D.δR v ψ (D.pval x' l') (D.pval x l • m) := by
  have hdv : ∀ (y : D.Q.V) (r : List D.Q.A), D.Q.pend y r ≠ v → D.dR v ψ y r = 0 := by
    intro y r hr
    rcases eq_nil_or_snoc r with rfl | ⟨r', c, rfl⟩
    · rfl
    · rw [dR_concat, hψv c (by rwa [D.pend_concat] at hr), LinearMap.zero_comp]
  rw [D.δR_pval hψe hψf hq x l, D.δR_pval hψe hψf hq x' l', D.pval_mul_pval]
  rcases eq_nil_or_snoc l' with rfl | ⟨l0, b, rfl⟩
  · -- `l' = []`: the vertex `e_{x'}`
    rw [dR_nil, LinearMap.zero_apply, add_zero]
    show _ = D.e x' • _
    rw [D.e_smul_simple]
    split_ifs with hpe hxv hxv
    · rw [List.append_nil, D.δR_pval hψe hψf hq]
    · rw [List.append_nil, D.δR_pval hψe hψf hq, hdv x l (by rwa [hpe])]; rfl
    · rw [map_zero, LinearMap.zero_apply, hdv x l (by rwa [hxv] at hpe)]; rfl
    · rw [map_zero, LinearMap.zero_apply]
  · rw [D.pval_smul_simple v x' (by simp), zero_add, dR_concat, LinearMap.comp_apply, lsm_apply,
      ← mul_smul]
    split_ifs with hpe
    · rw [D.δR_pval hψe hψf hq, ← List.append_assoc, dR_concat, LinearMap.comp_apply, lsm_apply,
        D.pval_append', hpe]
    · rw [map_zero, LinearMap.zero_apply, D.pval_mul_pval, if_neg hpe, zero_smul, map_zero]

include hψv hψe hψf in
/-- **The derivation rule.** -/
theorem δR_mem_cocycles (hq : D.IsQuadratic) :
    D.δR v ψ ∈ Ext1.cocycles k B M (D.simple v) := by
  have hspan : ∀ a : B, a ∈ Submodule.span k
      (Set.range fun p : D.Q.V × List D.Q.A ↦ D.pval p.1 p.2) := fun a ↦ by
    rw [D.span_pval]; trivial
  -- first for paths `b`, all `a`
  have h1 : ∀ (x : D.Q.V) (l : List D.Q.A) (a : B) (m : M),
      D.δR v ψ (a * D.pval x l) m =
        a • D.δR v ψ (D.pval x l) m + D.δR v ψ a (D.pval x l • m) := by
    intro x l a
    induction hspan a using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨⟨x', l'⟩, rfl⟩ := ha
        exact D.δR_leibniz_pval hψv hψe hψf hq x x' l l'
    | zero => intro m; simp
    | add a a' _ _ ha ha' =>
        intro m
        rw [add_mul, map_add, LinearMap.add_apply, ha, ha', add_smul, map_add,
          LinearMap.add_apply]
        abel
    | smul c a _ ha =>
        intro m
        have e1 : D.δR v ψ ((c • a) * D.pval x l) m = c • D.δR v ψ (a * D.pval x l) m := by
          rw [smul_mul_assoc, (D.δR v ψ).map_smul c (a * D.pval x l)]; rfl
        have e2 : D.δR v ψ (c • a) (D.pval x l • m) = c • D.δR v ψ a (D.pval x l • m) := by
          rw [(D.δR v ψ).map_smul c a]; rfl
        rw [e1, e2, ha m, smul_add, smul_assoc]
  intro a b
  induction hspan b using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨⟨x, l⟩, rfl⟩ := hb
      exact h1 x l a
  | zero => intro m; simp
  | add b b' _ _ hb hb' =>
      intro m
      rw [mul_add, map_add, LinearMap.add_apply, hb, hb', map_add, LinearMap.add_apply, add_smul,
        smul_add, map_add]
      abel
  | smul c b _ hb =>
      intro m
      have e1 : D.δR v ψ (a * (c • b)) m = c • D.δR v ψ (a * b) m := by
        rw [mul_smul_comm, (D.δR v ψ).map_smul c (a * b)]; rfl
      have e2 : D.δR v ψ (c • b) m = c • D.δR v ψ b m := by
        rw [(D.δR v ψ).map_smul c b]; rfl
      rw [e1, e2, hb m, smul_add, smul_comm c a, smul_assoc, (D.δR v ψ a).map_smul c (b • m)]

theorem δR_e (x : D.Q.V) : D.δR v ψ (D.e x) = 0 := by
  have : D.e x = D.basis ⟨(x, []), D.e_ne x⟩ := (D.basis_apply ⟨(x, []), D.e_ne x⟩).symm
  rw [this, δR, Basis.constr_basis]
  rfl

include hψe in
theorem δR_α (hq : D.IsQuadratic) (a : D.Q.A) : D.δR v ψ (D.α a) = ψ a := by
  have h := D.α_ne_zero hq a
  · have : D.α a = D.basis ⟨(D.Q.src a, [a]), by
        show D.toPathData.pval (D.Q.src a) [a] ≠ 0
        rw [D.toPathData.pval_single_src]; exact h⟩ := by
      rw [D.basis_apply]
      exact (D.toPathData.pval_single_src a).symm
    rw [this, δR, Basis.constr_basis]
    show D.dR v ψ (D.Q.src a) ([] ++ [a]) = ψ a
    rw [dR_concat]
    exact LinearMap.ext fun m ↦ hψe a m

end Right

variable (M) in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- **Lower bound for `Ext¹(M, S_v)`** over quadratic monomial data. -/
theorem finrank_ext1_simple_ge [FiniteDimensional k B] [FiniteDimensional k M]
    (hq : D.IsQuadratic) (v : D.Q.V) :
    ∑ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb M b.1) + finrank k (D.K0 M v) ≤
      finrank k (Ext1 k B M (D.simple v)) + finrank k (D.E0 M v) := by
  classical
  set S := D.simple v
  set Z := Ext1.cocycles k B M S
  set Bd := Ext1.coboundaries k B M S
  have hL : ∀ δ ∈ Z, ∀ a b m, δ (a * b) m = a • δ b m + δ a (b • m) := fun δ hδ ↦ hδ
  let Nz : Submodule k (B →ₗ[k] M →ₗ[k] S) :=
    { carrier := {δ | ∀ w, δ (D.e w) = 0}
      add_mem' := fun hδ hδ' w ↦ by simp [hδ w, hδ' w]
      zero_mem' := fun w ↦ by simp
      smul_mem' := fun c δ hδ w ↦ by simp [hδ w] }
  let N := Z ⊓ Nz
  have hExt : Ext1 k B M S = N.map Bd.mkQ := by
    apply le_antisymm
    · rintro _ ⟨δ, hδ, rfl⟩
      obtain ⟨φ, hφ⟩ := D.exists_normalized δ hδ
      refine ⟨δ - Ext1.inner k B M S φ, ⟨Z.sub_mem hδ (Ext1.range_inner_le k B M S ⟨φ, rfl⟩),
        hφ⟩, ?_⟩
      rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero Bd).mpr ⟨φ, rfl⟩, sub_zero]
    · exact Submodule.map_mono inf_le_left
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := k) (V := N)
    (V₂ := (B →ₗ[k] M →ₗ[k] S) ⧸ Bd) (Bd.mkQ.domRestrict N)
  rw [LinearMap.range_domRestrict, ← hExt, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hrn
  have hαe : ∀ δ ∈ N, ∀ b m, δ (D.α b) (D.e (D.Q.src b) • m) = δ (D.α b) m := by
    intro δ hδ b m
    have := hL δ hδ.1 (D.α b) (D.e (D.Q.src b)) m
    rw [D.toPathData.α_mul_e, hδ.2, LinearMap.zero_apply, smul_zero, zero_add] at this
    exact this.symm
  have hαα : ∀ δ ∈ N, ∀ a b, D.toPathData.Forbidden a b → ∀ m, δ (D.α b) (D.α a • m) = 0 := by
    intro δ hδ a b hab m
    have h0 : D.α b * D.α a = 0 := by
      have h := hab.2
      have e1 : D.toPathData.pval (D.Q.src a) [a, b] = D.toPathData.α b * D.toPathData.α a := by
        rw [show [a, b] = [a] ++ [b] from rfl, D.toPathData.pval_append,
          D.toPathData.pval_single_src, D.toPathData.pval_single]
        simp only [Statement.FinQuiver.pend]
        rw [mul_assoc, D.toPathData.e_mul_α]
      rw [e1] at h
      exact h
    have := hL δ hδ.1 (D.α b) (D.α a) m
    rw [h0, map_zero, LinearMap.zero_apply, D.α_smul_simple, zero_add] at this
    exact this.symm
  have hαv : ∀ δ ∈ N, ∀ b, D.Q.tgt b ≠ v → δ (D.α b) = 0 := by
    intro δ hδ b hb
    ext m
    have := hL δ hδ.1 (D.e (D.Q.tgt b)) (D.α b) m
    rw [D.toPathData.e_mul_α, hδ.2, LinearMap.zero_apply, add_zero, D.e_smul_simple,
      if_neg hb] at this
    exact this
  -- the injection into the product of the spaces `Z_b`
  let Θ : N →ₗ[k] ((b : {b : D.Q.A // D.Q.tgt b = v}) → D.Zb M b.1) :=
    { toFun := fun δ b ↦ ⟨fun m ↦ D.coord v (δ.1 (D.α b.1) m),
        ⟨fun x y ↦ by simp, fun c x ↦ by simp⟩,
        fun m ↦ by
          show D.coord v (δ.1 (D.α b.1) (D.e _ • m)) = D.coord v (δ.1 (D.α b.1) m)
          rw [hαe δ.1 δ.2],
        fun a hab m ↦ by
          show D.coord v (δ.1 (D.α b.1) (D.α a • m)) = 0
          rw [hαα δ.1 δ.2 a b.1 hab, map_zero]⟩
      map_add' := fun δ δ' ↦ by
        funext b; apply Subtype.ext; funext m
        show D.coord v ((δ.1 + δ'.1) (D.α b.1) m) =
          D.coord v (δ.1 (D.α b.1) m) + D.coord v (δ'.1 (D.α b.1) m)
        rw [LinearMap.add_apply, LinearMap.add_apply, map_add]
      map_smul' := fun c δ ↦ by
        funext b; apply Subtype.ext; funext m
        show D.coord v ((c • δ.1) (D.α b.1) m) = c * D.coord v (δ.1 (D.α b.1) m)
        rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, smul_eq_mul] }
  -- every admissible family comes from a normalized derivation
  have hΘs : Function.Surjective Θ := by
    intro ψf
    let ψ : D.Q.A → M →ₗ[k] S := fun b ↦
      if h : D.Q.tgt b = v then LinearMap.smulRight (toLin (ψf ⟨b, h⟩).1 (ψf ⟨b, h⟩).2.1) (D.s0 v)
      else 0
    have hψv : ∀ b, D.Q.tgt b ≠ v → ψ b = 0 := fun b hb ↦ by simp [ψ, hb]
    have hψe : ∀ b m, ψ b (D.e (D.Q.src b) • m) = ψ b m := by
      intro b m
      by_cases hb : D.Q.tgt b = v
      · simp only [ψ, dif_pos hb, LinearMap.smulRight_apply, toLin, LinearMap.coe_mk,
          AddHom.coe_mk]
        rw [(ψf ⟨b, hb⟩).2.2.1 m]
      · simp [ψ, hb]
    have hψf : ∀ a b, D.toPathData.Forbidden a b → ∀ m, ψ b (D.α a • m) = 0 := by
      intro a b hab m
      by_cases hb : D.Q.tgt b = v
      · simp only [ψ, dif_pos hb, LinearMap.smulRight_apply, toLin, LinearMap.coe_mk,
          AddHom.coe_mk]
        rw [(ψf ⟨b, hb⟩).2.2.2 a hab m, zero_smul]
      · simp [ψ, hb]
    have hδZ := D.δR_mem_cocycles hψv hψe hψf hq
    refine ⟨⟨D.δR v ψ, hδZ, fun w ↦ D.δR_e w⟩, ?_⟩
    funext b
    apply Subtype.ext
    funext m
    show D.coord v (D.δR v ψ (D.α b.1) m) = (ψf b).1 m
    rw [D.δR_α hψe hq]
    show D.coord v (ψ b.1 m) = (ψf b).1 m
    simp only [ψ, dif_pos b.2]
    show D.coord v ((ψf ⟨b.1, b.2⟩).1 m • D.s0 v) = (ψf b).1 m
    rw [map_smul, D.coord_s0, smul_eq_mul, mul_one]
  have hN : ∑ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb M b.1) ≤ finrank k N := by
    rw [← Module.finrank_pi_fintype]
    have h1 := LinearMap.finrank_range_le Θ
    rw [LinearMap.range_eq_top.mpr hΘs, finrank_top] at h1
    exact h1
  -- inner derivations of functionals supported at `v`
  let L : D.E0 M v → (M →ₗ[k] S) := fun φ ↦ LinearMap.smulRight (toLin φ.1 φ.2.1) (D.s0 v)
  have hinnerN : ∀ φ : D.E0 M v, Ext1.inner k B M S (L φ) ∈ N := by
    intro φ
    refine ⟨Ext1.range_inner_le k B M S ⟨_, rfl⟩, fun w ↦ ?_⟩
    ext m
    simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, LinearMap.zero_apply, toLin,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_comm, D.e_smul_simple]
    have hφw : φ.1 (D.e w • m) = if w = v then φ.1 m else 0 := by
      rw [← φ.2.2 (D.e w • m), ← mul_smul, D.toPathData.e_mul_e]
      by_cases h : w = v
      · subst h; simp [φ.2.2 m]
      · have h0 : φ.1 0 = 0 := (toLin φ.1 φ.2.1).map_zero
        simp [h, Ne.symm h, h0]
    rw [hφw]
    split_ifs <;> simp
  have hL_add : ∀ φ ψ : D.E0 M v, L (φ + ψ) = L φ + L ψ := by
    intro φ ψ; ext m; simp [L, toLin, add_smul]
  have hL_smul : ∀ (c : k) (φ : D.E0 M v), L (c • φ) = c • L φ := by
    intro c φ; ext m; simp [L, toLin, smul_smul]
  let ι : D.E0 M v →ₗ[k] N :=
    { toFun := fun φ ↦ ⟨Ext1.inner k B M S (L φ), hinnerN φ⟩
      map_add' := fun φ ψ ↦ by
        apply Subtype.ext
        show Ext1.inner k B M S (L (φ + ψ)) = Ext1.inner k B M S (L φ) + Ext1.inner k B M S (L ψ)
        rw [hL_add, map_add]
      map_smul' := fun c φ ↦ by
        apply Subtype.ext
        show Ext1.inner k B M S (L (c • φ)) = c • Ext1.inner k B M S (L φ)
        rw [hL_smul, map_smul] }
  -- functionals in `K₀` give zero inner derivations
  have hker : finrank k (D.K0 M v) ≤ finrank k (LinearMap.ker ι) := by
    have hzero : ∀ φ : D.K0 M v, ι ⟨φ.1, φ.2.1, φ.2.2.1⟩ = 0 := by
      intro φ
      apply Subtype.ext
      show Ext1.inner k B M S (L ⟨φ.1, φ.2.1, φ.2.2.1⟩) = 0
      refine D.eq_zero_of_normalized _ (Ext1.range_inner_le k B M S ⟨_, rfl⟩)
        (hinnerN ⟨φ.1, φ.2.1, φ.2.2.1⟩).2 fun a ↦ ?_
      ext m
      simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, D.α_smul_simple, zero_sub,
        toLin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
      have h0 : φ.1 (D.α a • m) = 0 := by
        by_cases ha : D.Q.tgt a = v
        · exact φ.2.2.2 a ha m
        · have hz : D.e v * D.α a = 0 := by
            have h1 : D.toPathData.e (D.Q.tgt a) * D.toPathData.α a = D.toPathData.α a :=
              D.toPathData.e_mul_α a
            calc D.e v * D.α a =
                D.toPathData.e v * (D.toPathData.e (D.Q.tgt a) * D.toPathData.α a) := by rw [h1]
              _ = 0 := by rw [← mul_assoc, D.toPathData.e_mul_e_of_ne (Ne.symm ha), zero_mul]
          rw [← φ.2.2.1, ← mul_smul, hz, zero_smul]
          exact (toLin φ.1 φ.2.1).map_zero
      rw [h0, zero_smul, neg_zero]
    let j : D.K0 M v →ₗ[k] LinearMap.ker ι :=
      { toFun := fun φ ↦ ⟨⟨φ.1, φ.2.1, φ.2.2.1⟩, hzero φ⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := j) fun φ ψ h ↦ ?_
    have h' := congrArg (fun x : LinearMap.ker ι ↦ ((x : D.E0 M v) : M → k)) h
    exact Subtype.ext h'
  -- normalized inner derivations come from functionals supported at `v`
  have hrange : Bd.comap N.subtype ≤ LinearMap.range ι := by
    rintro δ ⟨f, hf⟩
    have hfe : ∀ m, f (D.e v • m) = f m := by
      intro m
      have h1 := congrArg (fun g : B →ₗ[k] M →ₗ[k] S ↦ g (D.e v) m) hf
      simp only [Ext1.inner_apply] at h1
      have h0 : (N.subtype δ) (D.e v) = 0 := δ.2.2 v
      rw [h0, LinearMap.zero_apply, D.e_smul_simple, if_pos rfl, sub_eq_zero] at h1
      exact h1.symm
    let φ : D.E0 M v := ⟨fun m ↦ D.coord v (f m), ⟨fun x y ↦ by simp, fun c x ↦ by simp⟩,
      fun m ↦ by simp only [hfe]⟩
    refine ⟨φ, Subtype.ext ?_⟩
    show Ext1.inner k B M S (L φ) = δ.1
    rw [show (δ.1 : B →ₗ[k] M →ₗ[k] S) = Ext1.inner k B M S f from hf.symm]
    congr 1
    ext m
    simp only [L, LinearMap.smulRight_apply, toLin, LinearMap.coe_mk, AddHom.coe_mk, φ]
    exact (D.eq_coord_smul v (f m)).symm
  have hι := LinearMap.finrank_range_add_finrank_ker (K := k) (V := D.E0 M v) (V₂ := N) ι
  have e1 : finrank k (Ext1 k B M (D.simple v)) + finrank k (Bd.comap N.subtype) =
      finrank k N := hrn
  have e4 : finrank k (Bd.comap N.subtype) ≤ finrank k (LinearMap.range ι) :=
    Submodule.finrank_mono hrange
  omega

variable (M) in
theorem finrank_ext1_simple_eq [FiniteDimensional k B] [FiniteDimensional k M]
    (hq : D.IsQuadratic) (v : D.Q.V) :
    finrank k (Ext1 k B M (D.simple v)) + finrank k (D.E0 M v) =
      ∑ b : {b : D.Q.A // D.Q.tgt b = v}, finrank k (D.Zb M b.1) + finrank k (D.K0 M v) :=
  le_antisymm (D.finrank_ext1_simple_le M v) (D.finrank_ext1_simple_ge M hq v)

/-! ### Derivations into `Hom_k(S_v, M)` -/

section Left

variable (v : D.Q.V) (χ : D.Q.A → D.simple v →ₗ[k] M)

/-- The value of the derivation on a path `b p` with first arrow `b`: `p ∘ χ_b ∘ e_x`. -/
def dL (x : D.Q.V) : List D.Q.A → D.simple v →ₗ[k] M
  | [] => 0
  | b :: r => lsm (D.pval (D.Q.tgt b) r) ∘ₗ χ b ∘ₗ lsm (D.e x)

/-- The derivation, extended linearly from the path basis. -/
def δL : B →ₗ[k] D.simple v →ₗ[k] M :=
  D.basis.constr k fun p ↦ D.dL v χ p.1.1 p.1.2

variable {v χ} (hχv : ∀ b, D.Q.src b ≠ v → χ b = 0)
  (hχe : ∀ b s, D.e (D.Q.tgt b) • χ b s = χ b s)
  (hχf : ∀ b c, D.toPathData.Forbidden b c → ∀ s, D.α c • χ b s = 0)

/-- In quadratic monomial data, an arrow followed by a nonzero path is zero only through a
relation at the junction. -/
theorem forbidden_of_cons (hq : D.IsQuadratic) {b : D.Q.A} {r : List D.Q.A}
    (h0 : D.pval (D.Q.tgt b) r ≠ 0) (hz : D.pval (D.Q.src b) (b :: r) = 0) :
    ∃ c r', r = c :: r' ∧ D.toPathData.Forbidden b c := by
  rcases r with _ | ⟨c, r'⟩
  · exfalso
    apply D.α_ne_zero hq b
    have : D.toPathData.pval (D.Q.src b) [b] = 0 := hz
    rwa [D.toPathData.pval_single_src] at this
  · refine ⟨c, r', rfl, ?_⟩
    have hw := D.isWalk_of_pval_ne_zero (D.Q.tgt b) (c :: r') h0
    have hc : D.Q.src c = D.Q.tgt b := by simpa [Letter.src] using hw.1
    have hwb : D.Q.IsWalk (D.Q.src b) ((b :: c :: r').map (·, true)) :=
      ⟨by simp [Letter.src], by simpa [Letter.tgt] using hw⟩
    obtain ⟨i, hi, hf⟩ := (hq b (c :: r') hwb).mp hz
    rcases i with _ | i
    · exact hf
    · exfalso
      apply h0
      rw [← hc]
      refine (hq c r' (by rw [hc]; exact hw)).mpr ⟨i, by simp at hi ⊢; omega, ?_⟩
      simpa using hf

include hχv hχe hχf in
theorem dL_eq_zero (hq : D.IsQuadratic) {x : D.Q.V} {l : List D.Q.A} (h : D.pval x l = 0) :
    D.dL v χ x l = 0 := by
  rcases l with _ | ⟨b, r⟩
  · exact absurd h (D.e_ne x)
  refine LinearMap.ext fun s ↦ ?_
  show D.pval (D.Q.tgt b) r • χ b (D.e x • s) = 0
  by_cases hbx : D.Q.src b = x
  · subst hbx
    by_cases h0 : D.pval (D.Q.tgt b) r = 0
    · rw [h0, zero_smul]
    obtain ⟨c, r', rfl, hf⟩ := D.forbidden_of_cons hq h0 h
    show (D.toPathData.pval (D.Q.tgt c) r' * D.α c * D.e (D.Q.tgt b)) • _ = 0
    rw [mul_smul, mul_smul, hχe, hχf b c hf, smul_zero]
  · rw [D.e_smul_simple]
    split_ifs with hxv
    · rw [hχv b (by rwa [hxv] at hbx), LinearMap.zero_apply, smul_zero]
    · rw [map_zero, smul_zero]

include hχv hχe hχf in
theorem δL_pval (hq : D.IsQuadratic) (x : D.Q.V) (l : List D.Q.A) :
    D.δL v χ (D.pval x l) = D.dL v χ x l := by
  by_cases h : D.pval x l = 0
  · rw [h, map_zero, D.dL_eq_zero hχv hχe hχf hq h]
  · have : D.pval x l = D.basis ⟨(x, l), h⟩ := (D.basis_apply ⟨(x, l), h⟩).symm
    rw [this, δL, Basis.constr_basis]

include hχv hχe hχf in
/-- **The derivation rule on pairs of paths.** -/
theorem δL_leibniz_pval (hq : D.IsQuadratic) (x x' : D.Q.V) (l l' : List D.Q.A)
    (s : D.simple v) :
    D.δL v χ (D.pval x' l' * D.pval x l) s =
      D.pval x' l' • D.δL v χ (D.pval x l) s + D.δL v χ (D.pval x' l') (D.pval x l • s) := by
  rw [D.δL_pval hχv hχe hχf hq x l, D.δL_pval hχv hχe hχf hq x' l', D.pval_mul_pval]
  rcases l with _ | ⟨b, r⟩
  · -- `l = []`: the vertex `e_x`
    show _ = D.pval x' l' • (0 : M) + D.dL v χ x' l' (D.e x • s)
    rw [smul_zero, zero_add]
    rcases l' with _ | ⟨c, r'⟩
    · split_ifs <;> simp [dL, D.δL_pval hχv hχe hχf hq]
    · show _ = D.pval (D.Q.tgt c) r' • χ c (D.e x' • D.e x • s)
      split_ifs with hpe
      · have hx : x = x' := hpe
        subst hx
        rw [List.nil_append, D.δL_pval hχv hχe hχf hq, ← mul_smul, D.toPathData.e_idem]
        rfl
      · have hne : x ≠ x' := hpe
        rw [map_zero, LinearMap.zero_apply, ← mul_smul,
          D.toPathData.e_mul_e_of_ne (Ne.symm hne), zero_smul, map_zero, smul_zero]
  · rw [D.pval_smul_simple v x (by simp), map_zero, add_zero]
    show _ = D.pval x' l' • D.pval (D.Q.tgt b) r • χ b (D.e x • s)
    split_ifs with hpe
    · rw [D.δL_pval hχv hχe hχf hq, List.cons_append]
      show D.pval (D.Q.tgt b) (r ++ l') • χ b (D.e x • s) = _
      have hpe' : D.Q.pend (D.Q.tgt b) r = x' := hpe
      rw [D.pval_append', ← mul_smul, hpe']
    · have hpe' : ¬ D.Q.pend (D.Q.tgt b) r = x' := hpe
      rw [map_zero, LinearMap.zero_apply, ← mul_smul, D.pval_mul_pval, if_neg hpe', zero_smul]

include hχv hχe hχf in
/-- **The derivation rule.** -/
theorem δL_mem_cocycles (hq : D.IsQuadratic) :
    D.δL v χ ∈ Ext1.cocycles k B (D.simple v) M := by
  have hspan : ∀ a : B, a ∈ Submodule.span k
      (Set.range fun p : D.Q.V × List D.Q.A ↦ D.pval p.1 p.2) := fun a ↦ by
    rw [D.span_pval]; trivial
  have h1 : ∀ (x : D.Q.V) (l : List D.Q.A) (a : B) (s : D.simple v),
      D.δL v χ (a * D.pval x l) s =
        a • D.δL v χ (D.pval x l) s + D.δL v χ a (D.pval x l • s) := by
    intro x l a
    induction hspan a using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨⟨x', l'⟩, rfl⟩ := ha
        exact D.δL_leibniz_pval hχv hχe hχf hq x x' l l'
    | zero => intro s; simp
    | add a a' _ _ ha ha' =>
        intro s
        rw [add_mul, map_add, LinearMap.add_apply, ha, ha', add_smul, map_add,
          LinearMap.add_apply]
        abel
    | smul c a _ ha =>
        intro s
        have e1 : D.δL v χ ((c • a) * D.pval x l) s = c • D.δL v χ (a * D.pval x l) s := by
          rw [smul_mul_assoc, (D.δL v χ).map_smul c (a * D.pval x l)]; rfl
        have e2 : D.δL v χ (c • a) (D.pval x l • s) = c • D.δL v χ a (D.pval x l • s) := by
          rw [(D.δL v χ).map_smul c a]; rfl
        rw [e1, e2, ha s, smul_add, smul_assoc]
  intro a b
  induction hspan b using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨⟨x, l⟩, rfl⟩ := hb
      exact h1 x l a
  | zero => intro s; simp
  | add b b' _ _ hb hb' =>
      intro s
      rw [mul_add, map_add, LinearMap.add_apply, hb, hb', map_add, LinearMap.add_apply, add_smul,
        smul_add, map_add]
      abel
  | smul c b _ hb =>
      intro s
      have e1 : D.δL v χ (a * (c • b)) s = c • D.δL v χ (a * b) s := by
        rw [mul_smul_comm, (D.δL v χ).map_smul c (a * b)]; rfl
      have e2 : D.δL v χ (c • b) s = c • D.δL v χ b s := by
        rw [(D.δL v χ).map_smul c b]; rfl
      rw [e1, e2, hb s, smul_add, smul_comm c a, smul_assoc, (D.δL v χ a).map_smul c (b • s)]

theorem δL_e (x : D.Q.V) : D.δL v χ (D.e x) = 0 := by
  have : D.e x = D.basis ⟨(x, []), D.e_ne x⟩ := (D.basis_apply ⟨(x, []), D.e_ne x⟩).symm
  rw [this, δL, Basis.constr_basis]
  rfl

include hχv hχe in
theorem δL_α (hq : D.IsQuadratic) (a : D.Q.A) : D.δL v χ (D.α a) = χ a := by
  have h := D.α_ne_zero hq a
  have : D.α a = D.basis ⟨(D.Q.src a, [a]), by
      show D.toPathData.pval (D.Q.src a) [a] ≠ 0
      rw [D.toPathData.pval_single_src]; exact h⟩ := by
    rw [D.basis_apply]
    exact (D.toPathData.pval_single_src a).symm
  rw [this, δL, Basis.constr_basis]
  refine LinearMap.ext fun s ↦ ?_
  show D.e (D.Q.tgt a) • χ a (D.e (D.Q.src a) • s) = χ a s
  rw [hχe, D.e_smul_simple]
  split_ifs with ha
  · rfl
  · rw [hχv a ha]; rfl

end Left

variable (M) in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- **Lower bound for `Ext¹(S_v, M)`** over quadratic monomial data. -/
theorem finrank_ext1_simple_left_ge [FiniteDimensional k B] [FiniteDimensional k M]
    (hq : D.IsQuadratic) (v : D.Q.V) :
    ∑ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb M b.1) + finrank k (D.K0' M v) ≤
      finrank k (Ext1 k B (D.simple v) M) + finrank k (D.E0' M v) := by
  classical
  set S := D.simple v
  set Z := Ext1.cocycles k B S M
  set Bd := Ext1.coboundaries k B S M
  have hL : ∀ δ ∈ Z, ∀ a b s, δ (a * b) s = a • δ b s + δ a (b • s) := fun δ hδ ↦ hδ
  let Nz : Submodule k (B →ₗ[k] S →ₗ[k] M) :=
    { carrier := {δ | ∀ w, δ (D.e w) = 0}
      add_mem' := fun hδ hδ' w ↦ by simp [hδ w, hδ' w]
      zero_mem' := fun w ↦ by simp
      smul_mem' := fun c δ hδ w ↦ by simp [hδ w] }
  let N := Z ⊓ Nz
  have hExt : Ext1 k B S M = N.map Bd.mkQ := by
    apply le_antisymm
    · rintro _ ⟨δ, hδ, rfl⟩
      obtain ⟨φ, hφ⟩ := D.exists_normalized δ hδ
      refine ⟨δ - Ext1.inner k B S M φ, ⟨Z.sub_mem hδ (Ext1.range_inner_le k B S M ⟨φ, rfl⟩),
        hφ⟩, ?_⟩
      rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero Bd).mpr ⟨φ, rfl⟩, sub_zero]
    · exact Submodule.map_mono inf_le_left
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := k) (V := N)
    (V₂ := (B →ₗ[k] S →ₗ[k] M) ⧸ Bd) (Bd.mkQ.domRestrict N)
  rw [LinearMap.range_domRestrict, ← hExt, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hrn
  have hαe : ∀ δ ∈ N, ∀ b s, D.e (D.Q.tgt b) • δ (D.α b) s = δ (D.α b) s := by
    intro δ hδ b s
    have := hL δ hδ.1 (D.e (D.Q.tgt b)) (D.α b) s
    rw [D.toPathData.e_mul_α, hδ.2, LinearMap.zero_apply, add_zero] at this
    exact this.symm
  have hαα : ∀ δ ∈ N, ∀ b c, D.toPathData.Forbidden b c → ∀ s, D.α c • δ (D.α b) s = 0 := by
    intro δ hδ b c hbc s
    have := hL δ hδ.1 (D.α c) (D.α b) s
    rw [D.α_mul_α_of_forbidden hbc, map_zero, LinearMap.zero_apply, D.α_smul_simple,
      map_zero, add_zero] at this
    exact this.symm
  have hαv : ∀ δ ∈ N, ∀ b, D.Q.src b ≠ v → δ (D.α b) = 0 := by
    intro δ hδ b hb
    ext s
    have := hL δ hδ.1 (D.α b) (D.e (D.Q.src b)) s
    rw [D.toPathData.α_mul_e, hδ.2, LinearMap.zero_apply, smul_zero, zero_add,
      D.e_smul_simple, if_neg hb, map_zero] at this
    exact this
  let Θ : N →ₗ[k] ((b : {b : D.Q.A // D.Q.src b = v}) → D.Yb M b.1) :=
    { toFun := fun δ b ↦ ⟨δ.1 (D.α b.1) (D.s0 v), hαe δ.1 δ.2 b.1 _,
        fun c hc ↦ hαα δ.1 δ.2 b.1 c hc _⟩
      map_add' := fun δ δ' ↦ by
        funext b; apply Subtype.ext
        show (δ.1 + δ'.1) (D.α b.1) (D.s0 v) = δ.1 (D.α b.1) (D.s0 v) + δ'.1 (D.α b.1) (D.s0 v)
        rw [LinearMap.add_apply, LinearMap.add_apply]
      map_smul' := fun c δ ↦ by
        funext b; apply Subtype.ext
        show (c • δ.1) (D.α b.1) (D.s0 v) = c • δ.1 (D.α b.1) (D.s0 v)
        rw [LinearMap.smul_apply, LinearMap.smul_apply] }
  have hΘs : Function.Surjective Θ := by
    intro χf
    let χ : D.Q.A → S →ₗ[k] M := fun b ↦
      if h : D.Q.src b = v then LinearMap.smulRight (D.coord v) (χf ⟨b, h⟩).1 else 0
    have hχv : ∀ b, D.Q.src b ≠ v → χ b = 0 := fun b hb ↦ by simp [χ, hb]
    have hχe : ∀ b s, D.e (D.Q.tgt b) • χ b s = χ b s := by
      intro b s
      by_cases hb : D.Q.src b = v
      · simp only [χ, dif_pos hb, LinearMap.smulRight_apply]
        rw [smul_comm, (χf ⟨b, hb⟩).2.1]
      · simp [χ, hb]
    have hχf : ∀ b c, D.toPathData.Forbidden b c → ∀ s, D.α c • χ b s = 0 := by
      intro b c hbc s
      by_cases hb : D.Q.src b = v
      · simp only [χ, dif_pos hb, LinearMap.smulRight_apply]
        rw [smul_comm, (χf ⟨b, hb⟩).2.2 c hbc, smul_zero]
      · simp [χ, hb]
    refine ⟨⟨D.δL v χ, D.δL_mem_cocycles hχv hχe hχf hq, fun w ↦ D.δL_e w⟩, ?_⟩
    funext b
    apply Subtype.ext
    show D.δL v χ (D.α b.1) (D.s0 v) = (χf b).1
    rw [D.δL_α hχv hχe hq]
    show χ b.1 (D.s0 v) = (χf b).1
    simp only [χ, dif_pos b.2, LinearMap.smulRight_apply]
    show D.coord v (D.s0 v) • (χf ⟨b.1, b.2⟩).1 = (χf b).1
    rw [D.coord_s0, one_smul]
  have hN : ∑ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb M b.1) ≤ finrank k N := by
    rw [← Module.finrank_pi_fintype]
    have h1 := LinearMap.finrank_range_le Θ
    rw [LinearMap.range_eq_top.mpr hΘs, finrank_top] at h1
    exact h1
  let L : D.E0' M v → (S →ₗ[k] M) := fun u ↦ LinearMap.smulRight (D.coord v) u.1
  have hinnerN : ∀ u : D.E0' M v, Ext1.inner k B S M (L u) ∈ N := by
    intro u
    refine ⟨Ext1.range_inner_le k B S M ⟨_, rfl⟩, fun w ↦ ?_⟩
    ext s
    simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, LinearMap.zero_apply]
    rw [D.e_smul_simple, smul_comm]
    have hu : D.e w • u.1 = if w = v then u.1 else 0 := by
      rw [← u.2, ← mul_smul, D.toPathData.e_mul_e]
      by_cases h : w = v
      · subst h; simp
      · simp [h]
    rw [hu]
    split_ifs <;> simp
  let ι : D.E0' M v →ₗ[k] N :=
    { toFun := fun u ↦ ⟨Ext1.inner k B S M (L u), hinnerN u⟩
      map_add' := fun u u' ↦ by
        apply Subtype.ext
        show Ext1.inner k B S M (L (u + u')) = Ext1.inner k B S M (L u) + Ext1.inner k B S M (L u')
        rw [← map_add]; congr 1; ext s; simp [L, smul_add]
      map_smul' := fun c u ↦ by
        apply Subtype.ext
        show Ext1.inner k B S M (L (c • u)) = c • Ext1.inner k B S M (L u)
        rw [← map_smul]; congr 1; ext s; simp [L, smul_comm c] }
  have hker : finrank k (D.K0' M v) ≤ finrank k (LinearMap.ker ι) := by
    have hzero : ∀ u : D.K0' M v, ι ⟨u.1, u.2.1⟩ = 0 := by
      intro u
      apply Subtype.ext
      show Ext1.inner k B S M (L ⟨u.1, u.2.1⟩) = 0
      refine D.eq_zero_of_normalized _ (Ext1.range_inner_le k B S M ⟨_, rfl⟩)
        (hinnerN ⟨u.1, u.2.1⟩).2 fun a ↦ ?_
      ext s
      simp only [L, Ext1.inner_apply, LinearMap.smulRight_apply, D.α_smul_simple, map_zero,
        sub_zero, LinearMap.zero_apply]
      have h0 : D.α a • u.1 = 0 := by
        by_cases ha : D.Q.src a = v
        · exact u.2.2 a ha
        · have hz : D.α a * D.e v = 0 := by
            have h1 : D.toPathData.α a * D.toPathData.e (D.Q.src a) = D.toPathData.α a :=
              D.toPathData.α_mul_e a
            calc D.α a * D.e v =
                (D.toPathData.α a * D.toPathData.e (D.Q.src a)) * D.toPathData.e v := by rw [h1]
              _ = 0 := by rw [mul_assoc, D.toPathData.e_mul_e_of_ne ha, mul_zero]
          rw [← u.2.1, ← mul_smul, hz, zero_smul]
      rw [smul_comm, h0, smul_zero]
    let j : D.K0' M v →ₗ[k] LinearMap.ker ι :=
      { toFun := fun u ↦ ⟨⟨u.1, u.2.1⟩, hzero u⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := j) fun u u' h ↦ ?_
    have h' := congrArg (fun x : LinearMap.ker ι ↦ ((x : D.E0' M v) : M)) h
    exact Subtype.ext h'
  have hrange : Bd.comap N.subtype ≤ LinearMap.range ι := by
    rintro δ ⟨f, hf⟩
    have hfe : D.e v • f (D.s0 v) = f (D.s0 v) := by
      have h1 := congrArg (fun g : B →ₗ[k] S →ₗ[k] M ↦ g (D.e v) (D.s0 v)) hf
      simp only [Ext1.inner_apply] at h1
      have h0 : (N.subtype δ) (D.e v) = 0 := δ.2.2 v
      rw [h0, LinearMap.zero_apply, D.e_smul_simple, if_pos rfl, sub_eq_zero] at h1
      exact h1
    refine ⟨⟨f (D.s0 v), hfe⟩, Subtype.ext ?_⟩
    show Ext1.inner k B S M (L ⟨f (D.s0 v), hfe⟩) = δ.1
    rw [show (δ.1 : B →ₗ[k] S →ₗ[k] M) = Ext1.inner k B S M f from hf.symm]
    congr 1
    ext s
    simp only [L, LinearMap.smulRight_apply]
    rw [← map_smul, ← D.eq_coord_smul v s]
  have hι := LinearMap.finrank_range_add_finrank_ker (K := k) (V := D.E0' M v) (V₂ := N) ι
  have e1 : finrank k (Ext1 k B (D.simple v) M) + finrank k (Bd.comap N.subtype) =
      finrank k N := hrn
  have e4 : finrank k (Bd.comap N.subtype) ≤ finrank k (LinearMap.range ι) :=
    Submodule.finrank_mono hrange
  omega

variable (M) in
theorem finrank_ext1_simple_left_eq [FiniteDimensional k B] [FiniteDimensional k M]
    (hq : D.IsQuadratic) (v : D.Q.V) :
    finrank k (Ext1 k B (D.simple v) M) + finrank k (D.E0' M v) =
      ∑ b : {b : D.Q.A // D.Q.src b = v}, finrank k (D.Yb M b.1) + finrank k (D.K0' M v) :=
  le_antisymm (D.finrank_ext1_simple_left_le M v) (D.finrank_ext1_simple_left_ge M hq v)

end MonomialData

end BrickAccessibility
