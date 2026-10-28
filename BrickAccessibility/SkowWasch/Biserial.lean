module

public import BrickAccessibility.SkowWasch.Procedure

/-!
# Biserial projectives in element form

`BisAt i` says that `R e_i = A u₁ + A u₂` with `A u_t` uniserial (`LChain`) and `u_t = e_{s_t} u_t`.
It gives the chain property for every arrow starting at `i` (`lchain_of_bisAt`) and at most two
arrows starting at `i` (`out_of_bisAt`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

namespace SkowWasch

namespace BasicData

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] (B : BasicData k A)

/-- Element form of a biserial left projective `A e_i`. -/
def BisAt (i : Fin B.n) : Prop :=
  ∃ (u₁ u₂ : A) (s₁ s₂ : Fin B.n), B.e s₁ * u₁ = u₁ ∧ B.e s₂ * u₂ = u₂ ∧
    u₁ ∈ B.Re i ∧ u₂ ∈ B.Re i ∧ LChain u₁ ∧ LChain u₂ ∧
    ∀ y ∈ B.Re i, ∃ x₁ x₂ : A, y = x₁ * u₁ + x₂ * u₂

variable {B}

theorem term_mem {i l s : Fin B.n} {u : A} (hu : B.e s * u = u) (huR : u ∈ B.Re i) (x : A) :
    (s = l ∧ ∃ c : k, B.e l * x * u - c • u ∈ B.R * B.R) ∨ (s ≠ l ∧ B.e l * x * u ∈ B.R * B.R) := by
  by_cases hs : s = l
  · subst hs
    left
    obtain ⟨c, r, hr, -, hc⟩ := B.corner s x
    refine ⟨rfl, c, ?_⟩
    have : B.e s * x * u = B.e s * x * B.e s * u := by rw [mul_assoc (B.e s * x), hu]
    rw [this, hc, add_mul, smul_mul_assoc, hu, add_sub_cancel_left]
    exact mul_mem_sq hr huR.2
  · right
    refine ⟨hs, ?_⟩
    have : B.e l * x * u = B.e l * x * B.e s * u := by rw [mul_assoc (B.e l * x), hu]
    rw [this]
    exact mul_mem_sq (B.corner_mem (Ne.symm hs) x) huR.2

/-- An arrow from `i` to `l` is the top of one of the two uniserial pieces. -/
theorem top_of_bisAt {i l : Fin B.n} {u₁ u₂ : A} {s₁ s₂ : Fin B.n} (h1 : B.e s₁ * u₁ = u₁)
    (h2 : B.e s₂ * u₂ = u₂) (hu1 : u₁ ∈ B.Re i) (hu2 : u₂ ∈ B.Re i)
    (hspan : ∀ y ∈ B.Re i, ∃ x₁ x₂ : A, y = x₁ * u₁ + x₂ * u₂)
    {g : A} (hg : g ∈ B.Mk i l) (hg2 : g ∉ B.R * B.R) :
    (s₁ = l ∧ u₁ ∈ B.Mk i l ∧ u₁ ∉ B.R * B.R) ∨ (s₂ = l ∧ u₂ ∈ B.Mk i l ∧ u₂ ∉ B.R * B.R) := by
  have hgR : g ∈ B.Re i := ⟨B.e_right hg, hg.2⟩
  obtain ⟨x₁, x₂, hx⟩ := hspan g hgR
  have hgl : g = B.e l * x₁ * u₁ + B.e l * x₂ * u₂ := by
    rw [mul_assoc, mul_assoc, ← mul_add, ← hx, B.e_left hg]
  have hMk : ∀ {u : A} {s : Fin B.n}, B.e s * u = u → u ∈ B.Re i → s = l → u ∈ B.Mk i l :=
    fun hu huR hs ↦ ⟨by rw [← hs, hu, huR.1], huR.2⟩
  by_contra hno
  push Not at hno
  obtain ⟨hn1, hn2⟩ := hno
  apply hg2
  have hterm : ∀ {u : A} {s : Fin B.n} (x : A), B.e s * u = u → u ∈ B.Re i →
      (s = l → u ∈ B.Mk i l → u ∈ B.R * B.R) → B.e l * x * u ∈ B.R * B.R := by
    intro u s x hu huR hn
    rcases term_mem hu huR x with ⟨hs, c, hc⟩ | ⟨-, hc⟩
    · have hu2 := hn hs (hMk hu huR hs)
      have := Submodule.add_mem _ hc (Submodule.smul_mem _ c hu2)
      rwa [sub_add_cancel] at this
    · exact hc
  rw [hgl]
  exact Submodule.add_mem _ (hterm x₁ h1 hu1 hn1) (hterm x₂ h2 hu2 hn2)

theorem lchain_of_eq_mul {a g w : A} (hg : LChain g) (h : a = w * g) : LChain a := by
  intro p q
  subst h
  rcases hg (p * w) (q * w) with ⟨z, hz⟩ | ⟨z, hz⟩
  · left; exact ⟨z, by simpa [mul_assoc] using hz⟩
  · right; exact ⟨z, by simpa [mul_assoc] using hz⟩

theorem lchain_of_mul_eq {a g w : A} (hg : LChain g) (h : a = g * w) : LChain a := by
  intro p q
  subst h
  rcases hg p q with ⟨z, hz⟩ | ⟨z, hz⟩
  · left; exact ⟨z, by rw [← mul_assoc, hz, mul_assoc z, mul_assoc q]⟩
  · right; exact ⟨z, by rw [← mul_assoc, hz, mul_assoc z, mul_assoc p]⟩

variable (hX : B.ChainX)
include hX

/-- **Chains for arrows**: every arrow starting at a biserial vertex has `A a` uniserial. -/
theorem lchain_of_bisAt {i l : Fin B.n} (hb : B.BisAt i) {a : A} (ha : a ∈ B.Mk i l)
    (ha2 : a ∉ B.R * B.R) : LChain a := by
  obtain ⟨u₁, u₂, s₁, s₂, h1, h2, hu1, hu2, hc1, hc2, hspan⟩ := hb
  have key : ∀ {u : A}, LChain u → u ∈ B.Mk i l → u ∉ B.R * B.R → LChain a := by
    intro u hu huM huR
    rcases B.one_sided hX huM huR with hl | hr
    · obtain ⟨w, hw⟩ := hl a ha; exact lchain_of_eq_mul hu hw
    · obtain ⟨w, hw⟩ := hr a ha; exact lchain_of_mul_eq hu hw
  rcases top_of_bisAt h1 h2 hu1 hu2 hspan ha ha2 with ⟨-, hm, hn⟩ | ⟨-, hm, hn⟩
  · exact key hc1 hm hn
  · exact key hc2 hm hn

omit hX in
/-- **At most two arrows** start at a biserial vertex. -/
theorem out_of_bisAt {i : Fin B.n} (hb : B.BisAt i) {l₁ l₂ l₃ : Fin B.n} (h1 : B.Arr i l₁)
    (h2 : B.Arr i l₂) (h3 : B.Arr i l₃) : l₁ = l₂ ∨ l₁ = l₃ ∨ l₂ = l₃ := by
  obtain ⟨u₁, u₂, s₁, s₂, e1, e2, hu1, hu2, -, -, hspan⟩ := hb
  have hs : ∀ {l}, B.Arr i l → s₁ = l ∨ s₂ = l := by
    rintro l ⟨g, hg, hg2⟩
    rcases top_of_bisAt e1 e2 hu1 hu2 hspan hg hg2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hs h1 with e1 | e1 <;> rcases hs h2 with e2 | e2 <;> rcases hs h3 with e3 | e3 <;>
    first
    | exact Or.inl (e1.symm.trans e2)
    | exact Or.inr (Or.inl (e1.symm.trans e3))
    | exact Or.inr (Or.inr (e2.symm.trans e3))

end BasicData

end SkowWasch

end BrickAccessibility
