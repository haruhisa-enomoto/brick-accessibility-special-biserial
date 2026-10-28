module

public import BrickAccessibility.Quiver.Classes
public import BrickAccessibility.Statement
public import BrickAccessibility.SkowWasch.Existence
public import BrickAccessibility.SkowWasch.Jans
public import BrickAccessibility.SkowWasch.BiserialModule
public import BrickAccessibility.SkowWasch.Opposite
public import BrickAccessibility.SkowWasch.Assemble

/-!
# Skowroński–Waschbüsch: representation-finite biserial algebras are special biserial

Over an algebraically closed field, a basic representation-finite biserial algebra `Λ`
carries admissible special biserial path data on `Λᵐᵒᵖ` (Skowroński–Waschbüsch, Lemma 2,
with Jans' theorem that representation-finite algebras are distributive and Kupisch's
description of distributive algebras).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

/-- **Skowroński–Waschbüsch**, in the form used for Corollary 5.6. -/
theorem exists_specialBiserial_pathData (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u)
    [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] (hbasic : IsBasic k Λ)
    (hrf : IsRepresentationFinite Λ) (hbis : IsBiserial Λ) :
    ∃ (Q : FinQuiver) (D : PathData Q Λᵐᵒᵖ),
      Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤ ∧
        D.IsAdmissible ∧ D.IsSpecialBiserial ∧
        ∀ (c : Q.V → k) (d : Q.A → k),
          ∑ v, c v • D.e v + ∑ a, d a • D.α a ∈ D.RadGe k 2 → c = 0 ∧ d = 0 := by
  open SkowWasch SkowWasch.BasicData in
  have : FiniteDimensional k Λᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv k : Λ ≃ₗ[k] Λᵐᵒᵖ)
  obtain ⟨B⟩ := exists_basicData (k := k) (A := Λᵐᵒᵖ) hbasic
  have hX : B.ChainX := fun i j z z' hz hz' ↦ B.mem_Id_or_mem_Id hrf hz hz'
  have hL : ∀ i j a, a ∈ B.Mk i j → a ∉ B.R * B.R → LChain a := fun i j a ha ha2 ↦
    lchain_of_bisAt hX (B.bisAt_of_biserial hbis.1 i) ha ha2
  have hout : ∀ j l₁ l₂ l₃, B.Arr j l₁ → B.Arr j l₂ → B.Arr j l₃ →
      l₁ = l₂ ∨ l₁ = l₃ ∨ l₂ = l₃ := fun j l₁ l₂ l₃ h1 h2 h3 ↦
    out_of_bisAt (B.bisAt_of_biserial hbis.1 j) h1 h2 h3
  have hX' := B.chainX_unopB hX
  have hR : ∀ i j a, a ∈ B.Mk i j → a ∉ B.R * B.R → RChain a := by
    intro i j a ha ha2
    apply rchain_of_lchain
    have ha' : a.unop ∈ B.unopB.Mk j i := B.mem_Mk_unopB.mpr (by simpa using ha)
    have ha2' : a.unop ∉ B.unopB.R * B.unopB.R := fun h ↦ ha2 (by simpa using B.mem_sq_unopB.mp h)
    exact lchain_of_bisAt hX' (B.unopB.bisAt_of_biserial hbis.2 j) ha' ha2'
  have hin : ∀ j i₁ i₂ i₃, B.Arr i₁ j → B.Arr i₂ j → B.Arr i₃ j →
      i₁ = i₂ ∨ i₁ = i₃ ∨ i₂ = i₃ := fun j i₁ i₂ i₃ h1 h2 h3 ↦
    out_of_bisAt (B.unopB.bisAt_of_biserial hbis.2 j) (B.arr_unopB.mpr h1)
      (B.arr_unopB.mpr h2) (B.arr_unopB.mpr h3)
  obtain ⟨ρ, hρ, hS, hP⟩ := B.exists_good hX hin hout hL hR
  exact exists_pathData hX hin hout hρ hS hP

end BrickAccessibility
