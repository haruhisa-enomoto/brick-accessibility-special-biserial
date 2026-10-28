module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Semicontinuity of kernel dimension in a polynomial family

For a family of linear maps `T s = ∑ m < N, s ^ m • Q m`, the kernel dimension at
all but finitely many parameters is at most its value at one parameter
(`finite_lt_finrank_ker`). A nonvanishing minor at the given parameter is a
nonzero polynomial in `s`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open Module Polynomial Matrix

variable {k : Type*} [Field k] {E W : Type*} [AddCommGroup E] [Module k E] [AddCommGroup W]
  [Module k W] [FiniteDimensional k E]

/-- The polynomial family. -/
def polyFam (Q : ℕ → E →ₗ[k] W) (N : ℕ) (s : k) : E →ₗ[k] W := ∑ m ∈ Finset.range N, s ^ m • Q m

/-- **Lower semicontinuity of rank** in a polynomial family. -/
theorem finite_lt_finrank_ker (Q : ℕ → E →ₗ[k] W) (N : ℕ) (t₀ : k) :
    {s : k | finrank k (LinearMap.ker (polyFam Q N t₀)) < finrank k (LinearMap.ker (polyFam Q N s))}.Finite := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = polyFam Q N := ⟨_, rfl⟩
  rw [← hT]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker (T t₀))
  obtain ⟨r, hr⟩ : ∃ r, r = finrank k C := ⟨_, rfl⟩
  let c : Basis (Fin r) k C := (Module.finBasis k C).reindex (finCongr hr.symm)
  -- the images of the basis of `C` are independent at `t₀`
  have hinj : Function.Injective ((T t₀).comp C.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have h1 : (x : E) ∈ LinearMap.ker (T t₀) := hx
    have := hC.inf_eq_bot
    have h2 : (x : E) ∈ LinearMap.ker (T t₀) ⊓ C := ⟨h1, x.2⟩
    rw [this] at h2
    exact (Submodule.mem_bot k).mpr (Subtype.ext ((Submodule.mem_bot k).mp h2))
  obtain ⟨u, hu⟩ : ∃ u : Fin r → W, u = fun j ↦ T t₀ (c j) := ⟨_, rfl⟩
  have hli : LinearIndependent k u := by
    rw [hu]; exact c.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinj)
  -- dual functionals
  have hφ : ∀ i : Fin r, ∃ φ : W →ₗ[k] k, ∀ j, φ (u j) = if i = j then 1 else 0 := by
    intro i
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Basis.span hli).coord i)
    refine ⟨φ, fun j ↦ ?_⟩
    have h1 := LinearMap.congr_fun hφ ((Basis.span hli) j)
    rw [LinearMap.comp_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply] at h1
    have h2 : (((Basis.span hli) j : Submodule.span k (Set.range u)) : W) = u j := by
      rw [Basis.span_apply]
    rw [← h2]
    simp only [Submodule.coe_subtype] at h1
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  choose φ hφ using hφ
  rw [hu] at hφ
  -- the minor
  let Mp : Matrix (Fin r) (Fin r) k[X] := Matrix.of fun i j ↦
    ∑ m ∈ Finset.range N, Polynomial.C (φ i (Q m (c j))) * X ^ m
  have heval : ∀ s, (Polynomial.evalRingHom s).mapMatrix Mp =
      Matrix.of fun i j ↦ φ i (T s (c j)) := by
    intro s
    ext i j
    rw [hT, RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [Mp, Matrix.of_apply, polyFam, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.sum_congr rfl fun m _ ↦ mul_comm _ _
  set p := Mp.det
  have hp0 : p.eval t₀ = 1 := by
    have := (Polynomial.evalRingHom t₀).map_det Mp
    rw [heval] at this
    have hI : (Matrix.of fun i j ↦ φ i (T t₀ (c j))) = (1 : Matrix (Fin r) (Fin r) k) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.one_apply]
      exact hφ i j
    rw [hI, Matrix.det_one] at this
    exact this
  have hp : p ≠ 0 := fun h ↦ by rw [h, Polynomial.eval_zero] at hp0; exact zero_ne_one hp0
  refine (Polynomial.finite_setOfPred_isRoot hp).subset fun s hs ↦ ?_
  by_contra hroot
  have hdet : (Matrix.of fun i j ↦ φ i (T s (c j))).det ≠ 0 := by
    have := (Polynomial.evalRingHom s).map_det Mp
    rw [heval] at this
    rw [← this]; exact hroot
  -- `T s` is injective on `C`
  have hinj' : LinearMap.ker (T s) ⊓ C = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    set a := c.repr ⟨x, hx2⟩
    have hxa : (⟨x, hx2⟩ : C) = ∑ j, a j • c j := (c.sum_repr _).symm
    have hmv : (Matrix.of fun i j ↦ φ i (T s (c j))) *ᵥ (fun j ↦ a j) = 0 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      have h0 : T s x = 0 := hx1
      have : x = ∑ j, a j • (c j : E) := by
        have := congrArg Subtype.val hxa
        simpa using this
      rw [this, map_sum] at h0
      have := congrArg (φ i) h0
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    have ha := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
    have : (⟨x, hx2⟩ : C) = 0 := by
      rw [hxa]
      simp only [show ∀ j, a j = 0 from fun j ↦ congrFun ha j, zero_smul, Finset.sum_const_zero]
    exact (Submodule.mem_bot k).mpr (congrArg Subtype.val this)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (T s)) C
  rw [hinj', finrank_bot] at h1
  have h2 := Submodule.finrank_add_eq_of_isCompl hC
  have h3 := Submodule.finrank_le (LinearMap.ker (T s) ⊔ C)
  simp only [Set.mem_ofPred_eq] at hs
  omega

end BrickAccessibility
