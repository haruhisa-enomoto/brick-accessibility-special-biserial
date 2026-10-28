module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Polynomial functions and covers by polynomial images

A function `(σ → k) → k` is polynomial if it is evaluation of a multivariate
polynomial. A map into a vector space is polynomial if all its linear
functionals are. The main result, `not_univ_subset_iUnion_range`, says that over
an infinite field a vector space of dimension `r` is not covered by finitely
many images of polynomial maps from affine spaces of dimension less than `r`.

This replaces the dimension theory of constructible sets in Step 1 of the
manuscript's Proposition 2.1.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open MvPolynomial

variable {k : Type*} [Field k]

theorem eval_bind₁_eq {σ τ : Type*} (x : τ → k) (q : σ → MvPolynomial τ k)
    (p : MvPolynomial σ k) : eval x (bind₁ q p) = eval (fun i ↦ eval x (q i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- A polynomial function on the affine space `σ → k`. -/
def IsPolyFun {σ : Type*} (f : (σ → k) → k) : Prop :=
  ∃ p : MvPolynomial σ k, ∀ x, f x = eval x p

namespace IsPolyFun

variable {σ : Type*}

theorem const (c : k) : IsPolyFun (fun _ : σ → k ↦ c) := ⟨C c, fun _ ↦ by simp⟩

theorem var (i : σ) : IsPolyFun (fun x : σ → k ↦ x i) := ⟨X i, fun _ ↦ by simp⟩

theorem add {f g : (σ → k) → k} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun (fun x ↦ f x + g x) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x ↦ by simp [hp, hq]⟩

theorem mul {f g : (σ → k) → k} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun (fun x ↦ f x * g x) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x ↦ by simp [hp, hq]⟩

theorem neg {f : (σ → k) → k} (hf : IsPolyFun f) : IsPolyFun (fun x ↦ -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x ↦ by simp [hp]⟩

theorem sub {f g : (σ → k) → k} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun (fun x ↦ f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem sum {ι : Type*} (s : Finset ι) {f : ι → (σ → k) → k}
    (hf : ∀ i ∈ s, IsPolyFun (f i)) : IsPolyFun (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (σ := σ) (0 : k)
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (s : Finset ι) {f : ι → (σ → k) → k}
    (hf : ∀ i ∈ s, IsPolyFun (f i)) : IsPolyFun (fun x ↦ ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (σ := σ) (1 : k)
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem smul_const {f : (σ → k) → k} (hf : IsPolyFun f) (c : k) :
    IsPolyFun (fun x ↦ c * f x) := (const c).mul hf

/-- The determinant of a matrix of polynomial functions is polynomial. -/
theorem det {n : Type*} [Fintype n] [DecidableEq n] {F : (σ → k) → Matrix n n k}
    (hF : ∀ i j, IsPolyFun (fun x ↦ F x i j)) : IsPolyFun (fun x ↦ (F x).det) := by
  simp only [Matrix.det_apply]
  refine sum _ fun τ _ ↦ ?_
  have : IsPolyFun (fun x ↦ ∏ i, F x (τ i) i) := prod _ fun i _ ↦ hF _ _
  obtain ⟨p, hp⟩ := this
  refine ⟨((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ k) * p, fun x ↦ ?_⟩
  have hpx := hp x
  simp only at hpx
  simp only [Units.smul_def, zsmul_eq_mul, hpx, map_mul, map_intCast]

/-- The entries of the adjugate of a matrix of polynomial functions are
polynomial. -/
theorem adjugate {n : Type*} [Fintype n] [DecidableEq n] {F : (σ → k) → Matrix n n k}
    (hF : ∀ i j, IsPolyFun (fun x ↦ F x i j)) (i j : n) :
    IsPolyFun (fun x ↦ (F x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine det fun a b ↦ ?_
  by_cases ha : a = j
  · subst ha
    simp only [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst hb; simpa using const (σ := σ) (1 : k)
    · simpa [Pi.single_apply, hb] using const (σ := σ) (0 : k)
  · simpa [Matrix.updateRow_ne ha] using hF a b

/-- Composition with a linear map `k^τ → k^σ` followed by translation preserves
polynomiality. -/
theorem comp_affine {τ : Type*} {f : (σ → k) → k} (hf : IsPolyFun f)
    (g : (τ → k) → σ → k) (hg : ∀ i, IsPolyFun (fun y ↦ g y i)) :
    IsPolyFun (fun y ↦ f (g y)) := by
  obtain ⟨p, hp⟩ := hf
  choose q hq using hg
  refine ⟨bind₁ q p, fun y ↦ ?_⟩
  show f (g y) = _
  rw [hp, eval_bind₁_eq]
  have : g y = fun i ↦ eval y (q i) := funext fun i ↦ hq i y
  rw [this]

end IsPolyFun

/-- A map into a vector space is polynomial if every linear functional of it is
polynomial. -/
def IsPolyMap {σ W : Type*} [AddCommGroup W] [Module k W] (F : (σ → k) → W) : Prop :=
  ∀ φ : W →ₗ[k] k, IsPolyFun (fun x ↦ φ (F x))

theorem IsPolyMap.comp_linear {σ W W' : Type*} [AddCommGroup W] [Module k W]
    [AddCommGroup W'] [Module k W'] {F : (σ → k) → W} (hF : IsPolyMap F) (L : W →ₗ[k] W') :
    IsPolyMap (fun x ↦ L (F x)) := fun φ ↦ hF (φ ∘ₗ L)

/-- A map given by polynomial coefficients on a fixed finite family of vectors is
polynomial. -/
theorem IsPolyMap.sum_smul {σ W ι : Type*} [AddCommGroup W] [Module k W] [Fintype ι]
    (c : ι → (σ → k) → k) (hc : ∀ i, IsPolyFun (c i)) (v : ι → W) :
    IsPolyMap (fun x ↦ ∑ i, c i x • v i) := by
  intro φ
  simp only [map_sum, map_smul, smul_eq_mul]
  exact IsPolyFun.sum _ fun i _ ↦ (hc i).mul (IsPolyFun.const _)

/-- Multiplying a polynomial map by a new variable keeps it polynomial. -/
theorem IsPolyMap.option_smul {σ W : Type*} [AddCommGroup W] [Module k W]
    {F : (σ → k) → W} (hF : IsPolyMap F) :
    IsPolyMap (fun x : Option σ → k ↦ x none • F (fun i ↦ x (some i))) := by
  intro φ
  simp only [map_smul, smul_eq_mul]
  refine (IsPolyFun.var none).mul ?_
  exact (hF φ).comp_affine _ fun i ↦ IsPolyFun.var (some i)

/-- Polynomials in fewer variables than their number are algebraically
dependent. -/
theorem exists_ne_zero_eval_eq_zero {σ ι : Type*} [Fintype σ] [Fintype ι]
    (p : ι → MvPolynomial σ k) (h : Fintype.card σ < Fintype.card ι) :
    ∃ G : MvPolynomial ι k, G ≠ 0 ∧ ∀ x : σ → k, eval (fun i ↦ eval x (p i)) G = 0 := by
  have hdep : ¬ AlgebraicIndependent k p := by
    intro hind
    have h1 := hind.lift_cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain] at h1
    simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, Nat.cast_le] at h1
    omega
  rw [algebraicIndependent_iff] at hdep
  obtain ⟨G, hG'⟩ := not_forall.mp hdep
  obtain ⟨hG, hG0⟩ := Classical.not_imp.mp hG'
  refine ⟨G, hG0, fun x ↦ ?_⟩
  have := congrArg (eval x) hG
  rw [map_zero] at this
  rw [← this, MvPolynomial.aeval_eq_bind₁, eval_bind₁_eq]

/-- **Covering lemma.** Over an infinite field, a vector space of dimension `r`
is not covered by finitely many images of polynomial maps from affine spaces of
dimension less than `r`. -/
theorem not_univ_subset_iUnion_range [Infinite k] {W : Type*} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {ι : Type*} [Finite ι] (σ : ι → Type*) [∀ i, Fintype (σ i)]
    (F : ∀ i, (σ i → k) → W) (hF : ∀ i, IsPolyMap (F i))
    (hdim : ∀ i, Fintype.card (σ i) < Module.finrank k W) :
    ¬ (Set.univ : Set W) ⊆ ⋃ i, Set.range (F i) := by
  classical
  have := Fintype.ofFinite ι
  intro hcov
  set r := Module.finrank k W
  let b := Module.finBasis k W
  -- coordinates of each map
  have hcoord : ∀ i (j : Fin r), IsPolyFun (fun x ↦ b.coord j (F i x)) :=
    fun i j ↦ hF i (b.coord j)
  choose p hp using hcoord
  have hG : ∀ i, ∃ G : MvPolynomial (Fin r) k, G ≠ 0 ∧
      ∀ x : σ i → k, eval (fun j ↦ b.coord j (F i x)) G = 0 := by
    intro i
    obtain ⟨G, hG0, hG⟩ := exists_ne_zero_eval_eq_zero (p i)
      (by simpa [Fintype.card_fin] using hdim i)
    refine ⟨G, hG0, fun x ↦ ?_⟩
    have hv : (fun j ↦ b.coord j (F i x)) = fun j ↦ eval x (p i j) := funext fun j ↦ hp i j x
    rw [hv]
    exact hG x
  choose G hG0 hGev using hG
  have hprod : (∏ i, G i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hG0 i
  apply hprod
  apply MvPolynomial.funext
  intro y
  rw [map_zero, map_prod]
  obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ (b.equivFun.symm y)))
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have := hGev i x
  rw [hx] at this
  have hv : (fun j ↦ b.coord j (b.equivFun.symm y)) = y := by
    funext j; simp [Finsupp.single_apply]
  rw [hv] at this
  exact this

end BrickAccessibility
