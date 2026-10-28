module

public import BrickAccessibility.Classification.BrickPieces
public import Mathlib.Data.Set.Finite.List

/-!
# Representation-finiteness without closed words

If a string algebra has no closed word with all cyclic adjacent pairs allowed,
then it is representation-finite (`isRepFinite_of_not_hasClosed`): an
indecomposable module is a single string piece with one-dimensional blocks, and
its string has no repeated letter, since a repeated letter cuts out an allowed
closed word. Band pieces are excluded because a band is an allowed closed word.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- An allowed closed word exists. -/
def MonomialData.HasClosed (D : MonomialData k B) : Prop :=
  ∃ (x : D.Q.V) (ω : List (Letter D.Q)) (hne : ω ≠ []), D.Q.IsWalk x ω ∧ D.Q.wend x ω = x ∧
    ω.IsChain D.AllowedPair ∧ D.AllowedPair (ω.getLast hne) (ω.head hne)

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)

include hA in
/-- Consecutive letters of a band without zero paths are allowed. -/
theorem allowed_succ (hK : b.KillsZero) (q : Fin b.n) :
    D.AllowedPair (b.lt q) (b.lt (b.succ q)) := by
  have hal := hA q
  rcases hl : b.lt q with ⟨a, d⟩
  rcases hl' : b.lt (b.succ q) with ⟨a', d'⟩
  rw [hl, hl'] at hal
  cases d <;> cases d'
  · -- `a⁻¹ a'⁻¹`: the path `a' a` from `succ (succ q)` to `q`
    rw [allowedPair_ff]
    intro hz
    have h1 : b.next a' (b.succ (b.succ q)) = some (b.succ q) :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inr ⟨by rw [pred_succ]; exact hl', by rw [pred_succ]⟩)
    have h2 : b.next a (b.succ q) = some q :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inr ⟨by rw [pred_succ]; exact hl, by rw [pred_succ]⟩)
    have := hK _ _ hz (b.succ (b.succ q)) (b.next_src a' _ _ h1)
    simp [followPos, h1, h2] at this
  · rw [allowedPair_ft]
    rintro rfl
    simp at hal
  · rw [allowedPair_tf]
    rintro rfl
    simp at hal
  · -- `a a'`: the path `a a'` from `q`
    rw [allowedPair_tt]
    intro hz
    have h1 : b.next a q = some (b.succ q) :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inl ⟨hl, rfl⟩)
    have h2 : b.next a' (b.succ q) = some (b.succ (b.succ q)) :=
      (b.next_eq_some_iff S hA _ _ _).mpr (Or.inl ⟨hl', rfl⟩)
    have := hK _ _ hz q (b.next_src a _ _ h1)
    simp [followPos, h1, h2] at this

include hA in
/-- A band without zero paths is an allowed closed word. -/
theorem hasClosed (hK : b.KillsZero) : D.HasClosed := by
  refine ⟨b.start, b.letters, b.ne, b.walk, b.closed, ?_, ?_⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    have hn : b.n = b.letters.length := rfl
    have := b.allowed_succ S hA hK ⟨i, by omega⟩
    rwa [show b.succ ⟨i, by omega⟩ = ⟨i + 1, by omega⟩ from Fin.ext (b.succ_val_of_lt _ (by omega))]
      at this
  · have := b.allowed_succ S hA hK b.last
    rw [succ_last] at this
    rwa [List.getLast_eq_getElem, List.head_eq_getElem]

end CWord

namespace Word

variable {D : MonomialData k B} (w : Word D.Q)

/-- A string with a repeated letter cuts out an allowed closed word. -/
theorem hasClosed_of_not_nodup (hs : w.IsString D) (hnd : ¬ w.letters.Nodup) : D.HasClosed := by
  rw [List.nodup_iff_injective_getElem] at hnd
  simp only [Function.Injective, not_forall] at hnd
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, he, hne⟩ := hnd
  have hlen : w.len = w.letters.length := rfl
  wlog hij : i < j generalizing i j
  · exact this j hj i hi he.symm (fun h ↦ hne h.symm) (by
      rcases Nat.lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with h | h
      · exact absurd h hij
      · exact h)
  set ω := (w.letters.drop i).take (j - i)
  have hωlen : ω.length = j - i := by simp [ω]; omega
  have hω : ∀ t (ht : t < ω.length), ω[t] = w.letters[i + t]'(by omega) := by
    intro t ht; simp [ω]
  have hne' : ω ≠ [] := by rw [← List.length_pos_iff]; omega
  have hwalk := isWalk_take_drop w.walk i
  have hdecomp : w.letters.drop i = ω ++ (w.letters.drop i).drop (j - i) := (List.take_append_drop _ _).symm
  rw [hdecomp, Statement.FinQuiver.isWalk_append] at hwalk
  refine ⟨w.vtx ⟨i, by omega⟩, ω, hne', hwalk.1, ?_, ?_, ?_⟩
  · -- the end vertex is `vtx j = src letters[j] = src letters[i] = vtx i`
    have h1 : D.Q.wend (w.vtx ⟨i, by omega⟩) ω = w.vtx ⟨j, by omega⟩ := by
      show D.Q.wend (D.Q.wend w.start (w.letters.take i)) ω = D.Q.wend w.start (w.letters.take j)
      rw [← Statement.FinQuiver.wend_append]
      congr 1
      rw [show j = i + (j - i) by omega, List.take_add]
    rw [h1, ← w.src_letter j (by omega), ← w.src_letter i (by omega)]
    exact congrArg Letter.src he.symm
  · exact ((chain_allowed w hs).drop i).take (j - i)
  · rw [List.getLast_eq_getElem, List.head_eq_getElem, hω _ (by omega), hω 0 (by omega)]
    have hc := (List.isChain_iff_getElem.mp (chain_allowed w hs)) (j - 1) (by omega)
    have e1 : i + (ω.length - 1) = j - 1 := by omega
    simp only [e1, Nat.add_zero]
    rw [show w.letters[i] = w.letters[j] from he]
    simpa [show j - 1 + 1 = j by omega] using hc

end Word

/-- An indecomposable product has exactly one factor. -/
theorem unique_of_isIndecomposable_pi {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module B (X i)] (hnt : ∀ i, Nontrivial (X i))
    (h : IsIndecomposable B (∀ i, X i)) : Nonempty (Unique ι) := by
  have := h.1
  have hne : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (∀ i, X i)
    exact hxy (funext fun i ↦ isEmptyElim i)
  have hsub : Subsingleton ι := by
    refine ⟨fun i j ↦ ?_⟩
    by_contra hij
    have hc : IsCompl (LinearMap.range (LinearMap.single B X i)) (LinearMap.ker (LinearMap.proj i)) := by
      constructor
      · rw [disjoint_iff, eq_bot_iff]
        rintro x ⟨⟨y, rfl⟩, hy⟩
        have : y = 0 := by simpa using hy
        simp [this]
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        refine Submodule.mem_sup.mpr ⟨Pi.single i (x i), ⟨x i, rfl⟩, x - Pi.single i (x i), ?_, by abel⟩
        simp
    rcases h.2 _ _ hc with h1 | h1
    · obtain ⟨x, hx⟩ := exists_ne (0 : X i)
      have : Pi.single i x ∈ LinearMap.range (LinearMap.single B X i) := ⟨x, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      have := congrFun this i
      simp at this
      exact hx this
    · obtain ⟨y, hy⟩ := exists_ne (0 : X j)
      have : Pi.single j y ∈ LinearMap.ker (LinearMap.proj (R := B) (φ := X) i) := by
        simp [Pi.single_eq_of_ne hij]
      rw [h1, Submodule.mem_bot] at this
      have := congrFun this j
      simp at this
      exact hy this
  exact ⟨@Unique.mk' ι (Classical.inhabited_of_nonempty hne) hsub⟩

namespace MonomialData.BlockQuiver

variable {D : MonomialData k B} {V : Type u} [AddCommGroup V] [Module k V]
  (C : D.BlockQuiver V) (hC : C.KillsZeroPaths)

/-- A nontrivial idempotent blockwise endomorphism decomposes a block module. -/
theorem not_isIndecomposable_of_idem [Nonempty C.P] (h : V →ₗ[k] V)
    (hcomm : ∀ a i y, h (C.g a i y) = C.g a i (h y)) (hidem : ∀ y, h (h y) = h y) (h0 : h ≠ 0)
    (h1 : h ≠ LinearMap.id) : ¬ IsIndecomposable B (C.Mod hC) := by
  intro hind
  let H : C.Mod hC →ₗ[B] C.Mod hC := C.withGHom hC C.g hC h hcomm
  have hH : ∀ p y, H (C.ofFun hC (Pi.single p y)) = C.ofFun hC (Pi.single p (h y)) :=
    fun p y ↦ C.withGHom_single hC C.g hC h hcomm p y
  have hHH : ∀ x, H (H x) = H x := by
    have : H.comp H = H := C.hom_ext hC fun p y ↦ by
      rw [LinearMap.comp_apply, hH, hH, hidem]
    exact fun x ↦ LinearMap.congr_fun this x
  obtain ⟨p⟩ := ‹Nonempty C.P›
  have hc : IsCompl (LinearMap.range H) (LinearMap.ker H) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨⟨y, rfl⟩, hy⟩
      have hy' : H (H y) = 0 := hy
      rw [hHH] at hy'
      exact (Submodule.mem_bot B).mpr hy'
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      refine Submodule.mem_sup.mpr ⟨H x, ⟨x, rfl⟩, x - H x, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hHH, sub_self]
  have hsingle : ∀ y, C.ofFun hC (Pi.single p y) = 0 → y = 0 := fun y hy ↦ by
    have : (Pi.single p y : C.P → V) p = 0 := congrFun hy p
    rwa [Pi.single_eq_same] at this
  rcases hind.2 _ _ hc with hr | hk
  · obtain ⟨y, hy⟩ : ∃ y, h y ≠ 0 := by
      by_contra hall; push Not at hall; exact h0 (LinearMap.ext hall)
    have : H (C.ofFun hC (Pi.single p y)) ∈ LinearMap.range H := ⟨_, rfl⟩
    rw [hr, Submodule.mem_bot, hH] at this
    exact hy (hsingle _ this)
  · obtain ⟨y, hy⟩ : ∃ y, h y ≠ y := by
      by_contra hall; push Not at hall; exact h1 (LinearMap.ext hall)
    have hk' : H (C.ofFun hC (Pi.single p (y - h y))) = 0 := by
      rw [hH, map_sub, hidem, sub_self, Pi.single_zero]; rfl
    have : C.ofFun hC (Pi.single p (y - h y)) ∈ LinearMap.ker H := hk'
    rw [hk, Submodule.mem_bot] at this
    exact hy (sub_eq_zero.mp (hsingle _ this)).symm

end MonomialData.BlockQuiver

/-- A rank-one idempotent on a space of dimension at least two. -/
theorem exists_rank_one_idem {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : 2 ≤ finrank k V) :
    ∃ h : V →ₗ[k] V, (∀ y, h (h y) = h y) ∧ h ≠ 0 ∧ h ≠ LinearMap.id := by
  let bV := Module.finBasis k V
  let i0 : Fin (finrank k V) := ⟨0, by omega⟩
  let i1 : Fin (finrank k V) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨(bV.coord i0).smulRight (bV i0), fun y ↦ ?_, fun h0 ↦ ?_, fun h1 ↦ ?_⟩
  · simp [Basis.coord_apply]
  · have := LinearMap.congr_fun h0 (bV i0)
    simp [Basis.coord_apply] at this
    exact bV.ne_zero i0 this
  · have := LinearMap.congr_fun h1 (bV i1)
    simp [Basis.coord_apply, Finsupp.single_apply, h01] at this
    exact bV.ne_zero i1 this.symm

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hs : w.IsString D)
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The blocks of an indecomposable string piece are one-dimensional. -/
theorem finrank_eq_one_of_isIndecomposable [FiniteDimensional k V] (hV : 0 < finrank k V)
    (hb : IsIndecomposable B ((w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs))) :
    finrank k V = 1 := by
  by_contra h1
  have h2 : 2 ≤ finrank k V := by omega
  have : Nonempty (w.blockQuiver V hs.1).P := ⟨(0 : Fin (w.len + 1))⟩
  obtain ⟨h, hidem, hh0, hh1⟩ := exists_rank_one_idem (k := k) h2
  exact (w.blockQuiver V hs.1).not_isIndecomposable_of_idem (w.blockQuiver_kills V hs) h
    (fun _ _ _ ↦ rfl) hidem hh0 hh1 hb

end Word

theorem isIndecomposable_of_equiv {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] (e : M ≃ₗ[B] N) (h : IsIndecomposable B M) : IsIndecomposable B N := by
  have := h.1
  refine ⟨e.symm.toEquiv.nontrivial, fun P R hPR ↦ ?_⟩
  have hc : IsCompl (P.comap e.toLinearMap) (R.comap e.toLinearMap) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have : e x ∈ P ⊓ R := hx
      rw [hPR.inf_eq_bot, Submodule.mem_bot] at this
      exact (Submodule.mem_bot B).mpr (by simpa using this)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp
        (show e x ∈ P ⊔ R by rw [hPR.sup_eq_top]; trivial)
      refine Submodule.mem_sup.mpr ⟨e.symm p, by simpa using hp, e.symm r, by simpa using hr, ?_⟩
      rw [← map_add, hpr, LinearEquiv.symm_apply_apply]
  rcases h.2 _ _ hc with h1 | h1
  · left
    refine eq_bot_iff.mpr fun y hy ↦ ?_
    have : e.symm y ∈ P.comap e.toLinearMap := by simpa using hy
    rw [h1, Submodule.mem_bot] at this
    simpa using congrArg e this
  · right
    refine eq_bot_iff.mpr fun y hy ↦ ?_
    have : e.symm y ∈ R.comap e.toLinearMap := by simpa using hy
    rw [h1, Submodule.mem_bot] at this
    simpa using congrArg e this

/-- **No allowed closed word ⇒ representation-finite** (for string algebras). -/
theorem isRepFinite_of_not_hasClosed [FiniteDimensional k B] (D : MonomialData k B)
    (hD : D.IsStringAlgebra) (h : ¬ D.HasClosed) : IsRepFinite B := by
  classical
  obtain ⟨S⟩ := MonomialData.exists_signs (D := D) hD.2
  set L := Fintype.card (Letter D.Q)
  let Str := {w : Word D.Q // w.IsString D ∧ w.letters.length ≤ L}
  have hfin : Finite Str := by
    have h1 : Finite {l : List (Letter D.Q) // l.length ≤ L} :=
      Set.finite_coe_iff.mpr (List.finite_length_le (Letter D.Q) L)
    let f : Str → D.Q.V × {l : List (Letter D.Q) // l.length ≤ L} :=
      fun w ↦ (w.1.start, ⟨w.1.letters, w.2.2⟩)
    refine Finite.of_injective f fun w w' e ↦ ?_
    obtain ⟨⟨s, l, hw⟩, hp⟩ := w
    obtain ⟨⟨s', l', hw'⟩, hp'⟩ := w'
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl
  let F : Str → ModuleCat.{u} B := fun w ↦ ModuleCat.of B (w.1.stringModule D w.2.1)
  let eS := Finite.equivFin Str
  refine ⟨Nat.card Str, F ∘ eS.symm, fun M _ _ _ hM ↦ ?_⟩
  let _ : Module k M := Module.compHom M (algebraMap k B)
  have : IsScalarTower k B M :=
    ⟨fun c b m ↦ by
      show (c • b) • m = algebraMap k B c • (b • m)
      rw [Algebra.smul_def, mul_smul]⟩
  have : FiniteDimensional k M := Module.Finite.trans B M
  obtain ⟨ι, hι, hιd, pc, ⟨e⟩⟩ := exists_decomposition S M
  have hX : IsIndecomposable B (∀ i, (pc i).X) := isIndecomposable_of_equiv e.symm hM
  obtain ⟨hU⟩ := unique_of_isIndecomposable_pi (fun i ↦ (pc i).nontriv) hX
  set i₀ : ι := default
  have e₁ : M ≃ₗ[B] (pc i₀).X := e.symm.trans (LinearEquiv.piUnique B fun i ↦ (pc i).X)
  have hXi : IsIndecomposable B (pc i₀).X := isIndecomposable_of_equiv e₁ hM
  rcases (pc i₀).kind with ⟨w, hs, V, _, _, _, hd, ⟨e₂⟩⟩ |
      ⟨b, hA, hK, hprim, V, _, _, _, φ, hd, ⟨e₂⟩⟩
  · have hV1 := w.finrank_eq_one_of_isIndecomposable hs (hd ▸ (pc i₀).d_pos)
      (isIndecomposable_of_equiv e₂ hXi)
    let eV : V ≃ₗ[k] k := LinearEquiv.ofFinrankEq _ _ (by rw [hV1, Module.finrank_self])
    obtain ⟨e₃⟩ := w.stringModule_equiv hs
    have hnd : w.letters.Nodup := by
      by_contra hnd; exact h (w.hasClosed_of_not_nodup hs hnd)
    have hlen : w.letters.length ≤ L := hnd.length_le_card
    refine ⟨eS ⟨w, hs, hlen⟩, ?_⟩
    rw [Function.comp_apply, Equiv.symm_apply_apply]
    exact ⟨e₁.trans (e₂.trans ((w.blockEquiv hs eV).trans e₃.symm))⟩
  · exact absurd (b.hasClosed S hA hK) h

end BrickAccessibility
