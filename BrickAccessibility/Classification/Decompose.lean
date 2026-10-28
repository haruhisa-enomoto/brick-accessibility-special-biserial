module

public import BrickAccessibility.Classification.Counts
public import BrickAccessibility.Classification.Additive

/-!
# The decomposition theorem

Every finite-dimensional module over a string algebra is a finite direct product
of string and band modules (`exists_decomposition`).

For each orbit of nonzero pairs we take one realization: a string or band module
`X` with a map to `M` inducing isomorphisms of the pair functors at all positions
(`Piece`). By the position counts, the pair functors of the product of the
pieces have the same dimensions as those of `M`; the dimension formula gives equal
dimensions, and the spanning lemma gives surjectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} (S : D.Signs)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- A module is the direct sum of its vertex spaces. -/
theorem finrank_eq_sum_vsp [FiniteDimensional k M] :
    finrank k M = ∑ v, finrank k (D.vsp M v) := by
  classical
  let e : M ≃ₗ[k] (∀ v, D.vsp M v) :=
    { toFun := fun x v ↦ ⟨D.e v • x, ⟨x, rfl⟩⟩
      map_add' := fun x y ↦ by funext v; ext; simp [smul_add]
      map_smul' := fun c x ↦ by funext v; ext; simp [smul_comm (D.e v) c x]
      invFun := fun y ↦ ∑ v, (y v : M)
      left_inv := fun x ↦ by
        simp only [← Finset.sum_smul, D.toPathData.sum_e, one_smul]
      right_inv := fun y ↦ by
        funext w; ext
        simp only [Finset.smul_sum]
        rw [Finset.sum_eq_single w]
        · exact (D.mem_vsp).mp (y w).2
        · intro v _ hv
          rw [BlockQuiver.e_smul_of_mem_vsp (y v).2, if_neg hv]
        · simp }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

variable {M}

/-- The dimension formula, summed over any finite set containing the supports. -/
theorem Signs.finrank_vsp_eq_sum_of_subset [FiniteDimensional k M] (v : D.Q.V) (s : Bool)
    (T : Finset (S.HW v s × S.HW v (!s)))
    (hT : (S.fam M v s).supp_finite.toFinset ×ˢ (S.fam M v (!s)).supp_finite.toFinset ⊆ T) :
    finrank k (D.vsp M v) = ∑ p ∈ T, (finrank k (S.pnum M v s p.1.1 p.2.1) -
      finrank k (S.pden M v s p.1.1 p.2.1)) := by
  rw [S.finrank_vsp_eq_sum M v s]
  refine Finset.sum_subset hT fun p _ hp ↦ ?_
  have hle : S.pnum M v s p.1.1 p.2.1 ≤ S.pden M v s p.1.1 p.2.1 := by
    rw [Finset.mem_product, not_and_or] at hp
    rcases hp with hp | hp
    · have hp' : p.1 ∉ (S.fam M v s).Supp := by simpa using hp
      exact IFam.num_le_den_of_not_mem (S.fam M v s) (S.fam M v (!s)) hp' p.2
    · have hp' : p.2 ∉ (S.fam M v (!s)).Supp := by simpa using hp
      exact IFam.num_le_den_of_not_mem' (S.fam M v s) (S.fam M v (!s)) hp' p.1
  have := Submodule.finrank_mono hle
  show finrank k (S.pnum M v s p.1.1 p.2.1) - finrank k (S.pden M v s p.1.1 p.2.1) = 0
  omega

end MonomialData

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (S : D.Signs)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

theorem num_eq_half (q : Fin (w.len + 1)) (s : Bool) :
    w.num S M q = S.pnum M (w.vtx q) s (.fin (w.half S q s)) (.fin (w.half S q (!s))) := by
  by_cases hs : s = w.sideSign S q
  · subst hs; rw [half_self, half_not]; rfl
  · rw [Bool.eq_not_iff.mpr hs, Bool.not_not, half_self, half_not, S.pnum_swap]; rfl

theorem den_eq_half (q : Fin (w.len + 1)) (s : Bool) :
    w.den S M q = S.pden M (w.vtx q) s (.fin (w.half S q s)) (.fin (w.half S q (!s))) := by
  by_cases hs : s = w.sideSign S q
  · subst hs; rw [half_self, half_not]; rfl
  · rw [Bool.eq_not_iff.mpr hs, Bool.not_not, half_self, half_not, S.pden_swap]; rfl

theorem den_le_num (hs : w.IsString D) (q : Fin (w.len + 1)) : w.den S M q ≤ w.num S M q := by
  rw [w.num_eq_half S M q true, w.den_eq_half S M q true]
  exact S.pden_le_pnum M (w.isHW_half hs S q true) (w.isHW_half hs S q false)

end Word

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

theorem numB_eq_half (q : Fin b.n) (s : Bool) :
    b.numB S M q = S.pnum M (b.vtx q) s (b.bhalf S q s) (b.bhalf S q (!s)) := by
  by_cases hs : s = S.st (b.lt q)
  · subst hs; rw [bhalf_self, bhalf_not]; rfl
  · rw [Bool.eq_not_iff.mpr hs, Bool.not_not, bhalf_self, bhalf_not, S.pnum_swap]; rfl

theorem denB_eq_half (q : Fin b.n) (s : Bool) :
    b.denB S M q = S.pden M (b.vtx q) s (b.bhalf S q s) (b.bhalf S q (!s)) := by
  by_cases hs : s = S.st (b.lt q)
  · subst hs; rw [bhalf_self, bhalf_not]; rfl
  · rw [Bool.eq_not_iff.mpr hs, Bool.not_not, bhalf_self, bhalf_not, S.pden_swap]; rfl

end CWord

/-! ### Pieces: realizations of orbits of nonzero pairs -/

variable {D : MonomialData k B}

open Classical in
/-- A string or band module mapping to `M`, inducing isomorphisms of the pair functors on
one orbit of pairs. -/
structure Piece (S : D.Signs) (M : Type u) [AddCommGroup M] [Module B M] [Module k M]
    [IsScalarTower k B M] where
  X : Type u
  [acg : AddCommGroup X]
  [modB : Module B X]
  [modk : Module k X]
  [tower : IsScalarTower k B X]
  [fd : FiniteDimensional k X]
  θ : X →ₗ[B] M
  nontriv : Nontrivial X
  Pos : Set (Pair D)
  d : ℕ
  d_pos : 0 < d
  orbit : ∀ P ∈ Pos, ∀ P', S.Orbit P P' ↔ P' ∈ Pos
  hX : ∀ (v : D.Q.V) (s : Bool) (h h' : HWord D.Q), S.Valid v s h → S.Valid v (!s) h' →
    finrank k (S.pnum X v s h h') - finrank k (S.pden X v s h h') =
      if (v, s, h, h') ∈ Pos then d else 0
  hM : ∀ P ∈ Pos, finrank k (S.pnum M P.1 P.2.1 P.2.2.1 P.2.2.2) -
    finrank k (S.pden M P.1 P.2.1 P.2.2.1 P.2.2.2) = d
  hsurj : ∀ P ∈ Pos, S.pnum M P.1 P.2.1 P.2.2.1 P.2.2.2 ≤
    LinearMap.range (θ.restrictScalars k) ⊔ S.pden M P.1 P.2.1 P.2.2.1 P.2.2.2
  kind : (∃ (w : Word D.Q) (hs : w.IsString D) (V : Type u) (_ : AddCommGroup V)
      (_ : Module k V) (_ : FiniteDimensional k V), finrank k V = d ∧
        Nonempty (X ≃ₗ[B] (w.blockQuiver V hs.1).Mod (w.blockQuiver_kills V hs))) ∨
    (∃ (b : CWord D.Q) (hA : b.Alt S) (hK : b.KillsZero)
      (_ : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) (V : Type u) (_ : AddCommGroup V)
      (_ : Module k V) (_ : FiniteDimensional k V) (φ : V ≃ₗ[k] V), finrank k V = d ∧
        Nonempty (X ≃ₗ[B] (b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ)))

attribute [instance] Piece.acg Piece.modB Piece.modk Piece.tower Piece.fd

variable (S : D.Signs) (M : Type u) [AddCommGroup M] [Module B M] [Module k M]
  [IsScalarTower k B M] [FiniteDimensional k M]

/-- The finrank of the image of an injective map. -/
theorem IsoOnto.finrank_sub {X V : Type*} [AddCommGroup X] [Module k X] [AddCommGroup V]
    [Module k V] [FiniteDimensional k X] {φ : V →ₗ[k] X} {n d : Submodule k X}
    (h : IsoOnto φ n d) (hdn : d ≤ n) : finrank k n - finrank k d = finrank k V := by
  rw [h.finrank_eq hdn, LinearMap.finrank_range_of_inj h.injective]; omega

/-- **The string piece** of a nonzero pair of finite half-words. -/
theorem exists_piece_fin {v : D.Q.V} {s : Bool} {L L' : List (Letter D.Q)}
    (h1 : S.IsHW v s L) (h2 : S.IsHW v (!s) L')
    (hne : ¬ S.pnum M v s (.fin L) (.fin L') ≤ S.pden M v s (.fin L) (.fin L')) :
    ∃ pc : Piece S M, ((v, s, .fin L, .fin L') : Pair D) ∈ pc.Pos := by
  classical
  set w := Word.join v L L' h1.1 h2.1
  have hs : w.IsString D := Word.join_isString h1.1 h2.1 S M h1 h2 hne
  set q := Word.jpos h1.1 h2.1
  have hq1 : w.half S q s = L := (Word.join_half h1.1 h2.1 S h1 h2).1
  have hq2 : w.half S q (!s) = L' := (Word.join_half h1.1 h2.1 S h1 h2).2
  have hvq : w.vtx q = v := Word.join_vtx_jpos h1.1 h2.1
  have hnum : w.num S M q = S.pnum M v s (.fin L) (.fin L') := by
    rw [w.num_eq_half S M q s, hvq, hq1, hq2]
  have hden : w.den S M q = S.pden M v s (.fin L) (.fin L') := by
    rw [w.den_eq_half S M q s, hvq, hq1, hq2]
  obtain ⟨W, hW1, hW2⟩ := IFam.exists_relCompl (S.pden_le_pnum (M := M)
    (h := .fin L) (h' := .fin L') h1 h2)
  have hWnum : ∀ y : W, W.subtype y ∈ w.num S M q := fun y ↦ by
    rw [hnum, ← hW1]; exact Submodule.mem_sup_left y.2
  obtain ⟨Θ, hΘ1, hΘ2⟩ := w.exists_stringHom hs S q W.subtype hWnum
  have hiso : IsoOnto (w.blockMap hs Θ q) (w.num S M q) (w.den S M q) := by
    refine ⟨fun y ↦ by rw [Word.blockMap_apply, hΘ1]; exact hWnum y, fun y hy ↦ ?_, ?_⟩
    · rw [Word.blockMap_apply, hΘ1, hden] at hy
      have : (y : M) ∈ W ⊓ S.pden M v s (.fin L) (.fin L') := ⟨y.2, hy⟩
      rw [hW2] at this
      exact Subtype.ext ((Submodule.mem_bot k).mp this)
    · rw [hnum, hden, ← hW1]
      refine sup_le_sup_right (fun x hx ↦ ⟨⟨x, hx⟩, ?_⟩) _
      rw [Word.blockMap_apply, hΘ1]; rfl
  have hall := w.iso_all hs S Θ hΘ2 q hiso
  have hdpos : 0 < finrank k W := by
    rcases Nat.eq_zero_or_pos (finrank k W) with h0 | h0
    · exfalso; apply hne
      rw [Submodule.finrank_eq_zero.mp h0, bot_sup_eq] at hW1
      rw [← hW1]
    · exact h0
  have hntW : Nontrivial W := Module.nontrivial_of_finrank_pos hdpos
  obtain ⟨y0, hy0⟩ := exists_ne (0 : W)
  refine ⟨{ X := (w.blockQuiver W hs.1).Mod (w.blockQuiver_kills W hs)
            θ := Θ
            nontriv := ⟨⟨(w.blockQuiver W hs.1).ofFun (w.blockQuiver_kills W hs) (Pi.single q y0), 0,
              fun h ↦ hy0 (by
                have : (Pi.single q y0 : Fin (w.len + 1) → W) q = 0 := congrFun h q
                rwa [Pi.single_eq_same] at this)⟩⟩
            Pos := w.Pos S
            d := finrank k W
            d_pos := hdpos
            orbit := fun P hP P' ↦ w.orbit_iff hs S hP P'
            hX := ?_
            hM := ?_
            hsurj := ?_
            kind := Or.inl ⟨w, hs, W, inferInstance, inferInstance, inferInstance, rfl,
              ⟨LinearEquiv.refl B _⟩⟩ }, ⟨q, s, ?_⟩⟩
  · intro v' s' h h' hv hv'
    rw [w.gr_eq hs S hv hv']
    have hc := w.card_eq S hs.1 (v', s', h, h')
    simp only at hc
    rw [hc]
    split_ifs <;> simp
  · rintro P ⟨q', s', rfl⟩
    have e1 : S.pnum M (w.pairAt S q' s').1 (w.pairAt S q' s').2.1 (w.pairAt S q' s').2.2.1
        (w.pairAt S q' s').2.2.2 = w.num S M q' := (w.num_eq_half S M q' s').symm
    have e2 : S.pden M (w.pairAt S q' s').1 (w.pairAt S q' s').2.1 (w.pairAt S q' s').2.2.1
        (w.pairAt S q' s').2.2.2 = w.den S M q' := (w.den_eq_half S M q' s').symm
    rw [e1, e2]
    exact (hall q').finrank_sub (w.den_le_num S M hs q')
  · rintro P ⟨q', s', rfl⟩
    have e1 : S.pnum M (w.pairAt S q' s').1 (w.pairAt S q' s').2.1 (w.pairAt S q' s').2.2.1
        (w.pairAt S q' s').2.2.2 = w.num S M q' := (w.num_eq_half S M q' s').symm
    have e2 : S.pden M (w.pairAt S q' s').1 (w.pairAt S q' s').2.1 (w.pairAt S q' s').2.2.1
        (w.pairAt S q' s').2.2.2 = w.den S M q' := (w.den_eq_half S M q' s').symm
    rw [e1, e2]
    refine (hall q').surj.trans (sup_le_sup_right ?_ _)
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · simp [Word.pairAt, hvq, hq1, hq2]

omit [FiniteDimensional k M] in
theorem CWord.denB_le_numB (b : CWord D.Q) (hA : b.Alt S) (q : Fin b.n) :
    b.denB S M q ≤ b.numB S M q :=
  S.pden_le_pnum M (b.valid_rightW S hA q) (b.valid_leftW S hA q)

/-- **The band piece** of a nonzero pair of infinite half-words. -/
theorem exists_piece_inf {v : D.Q.V} {s : Bool} {f g : ℕ → Letter D.Q}
    (hv : S.Valid v s (.inf f)) (hv' : S.Valid v (!s) (.inf g))
    (hne : ¬ S.pnum M v s (.inf f) (.inf g) ≤ S.pden M v s (.inf f) (.inf g)) :
    ∃ pc : Piece S M, ((v, s, .inf f, .inf g) : Pair D) ∈ pc.Pos := by
  classical
  obtain ⟨b, hA, hK, hprim, hvf, hsf, hRf, hLg⟩ := CWord.exists_band S M hv hv' hne
  subst hvf hsf hRf hLg
  change ¬ b.numB S M b.first ≤ b.denB S M b.first at hne
  obtain ⟨U, τ, hU1, hU2, hU3, hU4⟩ := b.exists_band_split S hA M b.first
  obtain ⟨Θ, hΘ1, hΘ2⟩ := b.exists_bandHom S hA hK U.subtype τ (fun y ↦ hU1 y.2) hU4
  have hiso : IsoOnto (b.bmap S hA τ hK Θ b.first) (b.numB S M b.first) (b.denB S M b.first) := by
    refine ⟨fun y ↦ by rw [CWord.bmap_apply, hΘ1]; exact hU1 y.2, fun y hy ↦ ?_, ?_⟩
    · rw [CWord.bmap_apply, hΘ1] at hy
      have : (y : M) ∈ U ⊓ b.denB S M b.first := ⟨y.2, hy⟩
      rw [hU2] at this
      exact Subtype.ext ((Submodule.mem_bot k).mp this)
    · rw [← hU3]
      refine sup_le_sup_right (fun x hx ↦ ⟨⟨x, hx⟩, ?_⟩) _
      rw [CWord.bmap_apply, hΘ1]; rfl
  have hall := b.iso_all S hA τ hK Θ hΘ2 hiso
  have hdpos : 0 < finrank k U := by
    rcases Nat.eq_zero_or_pos (finrank k U) with h0 | h0
    · exfalso; apply hne
      rw [Submodule.finrank_eq_zero.mp h0, bot_sup_eq] at hU3
      rw [← hU3]
    · exact h0
  have hntU : Nontrivial U := Module.nontrivial_of_finrank_pos hdpos
  obtain ⟨y0, hy0⟩ := exists_ne (0 : U)
  refine ⟨{ X := (b.blockQuiver S hA U τ).Mod (b.blockQuiver_kills S hA hK U τ)
            θ := Θ
            nontriv := ⟨⟨(b.blockQuiver S hA U τ).ofFun (b.blockQuiver_kills S hA hK U τ)
              (Pi.single b.first y0), 0, fun h ↦ hy0 (by
                have : (Pi.single b.first y0 : Fin b.n → U) b.first = 0 := congrFun h b.first
                rwa [Pi.single_eq_same] at this)⟩⟩
            Pos := b.Pos S
            d := finrank k U
            d_pos := hdpos
            orbit := fun P hP P' ↦ b.orbit_iff S hA hP P'
            hX := ?_
            hM := ?_
            hsurj := ?_
            kind := Or.inr ⟨b, hA, hK, hprim, U, inferInstance, inferInstance, inferInstance, τ, rfl,
              ⟨LinearEquiv.refl B _⟩⟩ }, ⟨b.first, S.st (b.lt b.first), ?_⟩⟩
  · intro v' s' h h' hv hv'
    rw [b.band_gr_eq S hA τ hK hv hv']
    have hc := b.card_eq S hA hprim (v', s', h, h')
    simp only at hc
    rw [hc]
    split_ifs <;> simp
  · rintro P ⟨q', s', rfl⟩
    have e1 : S.pnum M (b.pairAt S q' s').1 (b.pairAt S q' s').2.1 (b.pairAt S q' s').2.2.1
        (b.pairAt S q' s').2.2.2 = b.numB S M q' := (b.numB_eq_half S M q' s').symm
    have e2 : S.pden M (b.pairAt S q' s').1 (b.pairAt S q' s').2.1 (b.pairAt S q' s').2.2.1
        (b.pairAt S q' s').2.2.2 = b.denB S M q' := (b.denB_eq_half S M q' s').symm
    rw [e1, e2]
    exact (hall q').finrank_sub (b.denB_le_numB S M hA q')
  · rintro P ⟨q', s', rfl⟩
    have e1 : S.pnum M (b.pairAt S q' s').1 (b.pairAt S q' s').2.1 (b.pairAt S q' s').2.2.1
        (b.pairAt S q' s').2.2.2 = b.numB S M q' := (b.numB_eq_half S M q' s').symm
    have e2 : S.pden M (b.pairAt S q' s').1 (b.pairAt S q' s').2.1 (b.pairAt S q' s').2.2.1
        (b.pairAt S q' s').2.2.2 = b.denB S M q' := (b.denB_eq_half S M q' s').symm
    rw [e1, e2]
    refine (hall q').surj.trans (sup_le_sup_right ?_ _)
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · simp [CWord.pairAt, CWord.bhalf_self, CWord.bhalf_not]

/-- **Every nonzero pair has a piece.** -/
theorem exists_piece (P : Pair D) (hv : S.Valid P.1 P.2.1 P.2.2.1)
    (hv' : S.Valid P.1 (!P.2.1) P.2.2.2)
    (hne : ¬ S.pnum M P.1 P.2.1 P.2.2.1 P.2.2.2 ≤ S.pden M P.1 P.2.1 P.2.2.1 P.2.2.2) :
    ∃ pc : Piece S M, P ∈ pc.Pos := by
  obtain ⟨v, s, h, h'⟩ := P
  cases h with
  | fin L =>
      cases h' with
      | fin L' => exact exists_piece_fin S M hv hv' hne
      | inf g =>
          exfalso; apply hne
          have := S.le_of_inf_fin M (s := !s) hv' (by rwa [Bool.not_not])
          rwa [S.pnum_swap, S.pden_swap] at this
  | inf f =>
      cases h' with
      | fin L' => exact absurd (S.le_of_inf_fin M hv hv') hne
      | inf g => exact exists_piece_inf S M hv hv' hne

/-! ### Assembly -/

/-- The orbit setoid on pairs. -/
def MonomialData.Signs.orbitSetoid : Setoid (Pair D) := ⟨S.Orbit, Signs.Orbit.equivalence S⟩

theorem finrank_sub_eq_zero {X : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    {n d : Submodule k X} (h : n ≤ d) : finrank k n - finrank k d = 0 := by
  have := Submodule.finrank_mono h; omega

/-- **The decomposition theorem.** Every finite-dimensional module over a string algebra is
a finite product of string and band modules. -/
theorem exists_decomposition :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (pc : ι → Piece S M),
      Nonempty ((∀ i, (pc i).X) ≃ₗ[B] M) := by
  classical
  -- nonzero pairs
  let NZ : Set (Pair D) := {P | S.Valid P.1 P.2.1 P.2.2.1 ∧ S.Valid P.1 (!P.2.1) P.2.2.2 ∧
    ¬ S.pnum M P.1 P.2.1 P.2.2.1 P.2.2.2 ≤ S.pden M P.1 P.2.1 P.2.2.1 P.2.2.2}
  have hNZ : NZ.Finite := by
    refine ((Set.finite_univ (α := D.Q.V)).prod ((Set.finite_univ (α := Bool)).prod
      ((S.suppSet_finite M).prod (S.suppSet_finite M)))).subset ?_
    rintro ⟨v, s, h, h'⟩ ⟨hv, hv', hne⟩
    obtain ⟨m1, m2⟩ := S.mem_suppSet M hv hv' hne
    exact ⟨trivial, trivial, m1, m2⟩
  let st := S.orbitSetoid
  let C : Finset (Quotient st) := hNZ.toFinset.image (Quotient.mk st)
  have hrep : ∀ c : C, ∃ P, P ∈ NZ ∧ Quotient.mk st P = c.1 := by
    intro c
    obtain ⟨P, hP, e⟩ := Finset.mem_image.mp c.2
    exact ⟨P, hNZ.mem_toFinset.mp hP, e⟩
  choose rep hrepNZ hrepc using hrep
  have hpc : ∀ c : C, ∃ pc : Piece S M, rep c ∈ pc.Pos := fun c ↦
    exists_piece S M (rep c) (hrepNZ c).1 (hrepNZ c).2.1 (hrepNZ c).2.2
  choose pc hpcmem using hpc
  -- membership in the pieces
  have hmem : ∀ (c : C) (P : Pair D), S.Valid P.1 P.2.1 P.2.2.1 → S.Valid P.1 (!P.2.1) P.2.2.2 →
      (P ∈ (pc c).Pos ↔ P ∈ NZ ∧ Quotient.mk st P = c.1) := by
    intro c P hv hv'
    constructor
    · intro hP
      refine ⟨⟨hv, hv', fun hle ↦ ?_⟩, ?_⟩
      · have := (pc c).hM P hP
        rw [finrank_sub_eq_zero hle] at this
        exact (pc c).d_pos.ne this
      · rw [← hrepc c]
        exact Quotient.sound (((pc c).orbit _ (hpcmem c) P).mpr hP).symm
    · rintro ⟨-, e⟩
      rw [← hrepc c] at e
      exact ((pc c).orbit _ (hpcmem c) P).mp (Quotient.exact e).symm
  let X := ∀ c : C, (pc c).X
  let θ : X →ₗ[B] M := ∑ c, (pc c).θ ∘ₗ LinearMap.proj c
  -- pair functors agree in dimension
  have hF : ∀ (v : D.Q.V) (s : Bool) (h h' : HWord D.Q), S.Valid v s h → S.Valid v (!s) h' →
      finrank k (S.pnum X v s h h') - finrank k (S.pden X v s h h') =
        finrank k (S.pnum M v s h h') - finrank k (S.pden M v s h h') := by
    intro v s h h' hv hv'
    rw [finrank_pnum_pi, finrank_pden_pi, ← Finset.sum_tsub_distrib _ fun c _ ↦
      Submodule.finrank_mono (S.pden_le_pnum _ hv hv')]
    simp_rw [(pc _).hX v s h h' hv hv']
    by_cases hP : ((v, s, h, h') : Pair D) ∈ NZ
    · have hc : Quotient.mk st ((v, s, h, h') : Pair D) ∈ C :=
        Finset.mem_image_of_mem _ (hNZ.mem_toFinset.mpr hP)
      rw [Finset.sum_eq_single ⟨_, hc⟩]
      · rw [if_pos ((hmem ⟨_, hc⟩ _ hv hv').mpr ⟨hP, rfl⟩)]
        exact ((pc ⟨_, hc⟩).hM _ ((hmem ⟨_, hc⟩ _ hv hv').mpr ⟨hP, rfl⟩)).symm
      · intro c _ hne
        rw [if_neg]
        intro hm
        exact hne (Subtype.ext ((hmem c _ hv hv').mp hm).2.symm)
      · simp
    · rw [Finset.sum_eq_zero fun c _ ↦ if_neg fun hm ↦ hP ((hmem c _ hv hv').mp hm).1]
      have hle : S.pnum M v s h h' ≤ S.pden M v s h h' := by
        by_contra hle; exact hP ⟨hv, hv', hle⟩
      exact (finrank_sub_eq_zero hle).symm
  -- vertex dimensions agree
  have hvsp : ∀ v, finrank k (D.vsp X v) = finrank k (D.vsp M v) := by
    intro v
    let T := ((S.fam X v true).supp_finite.toFinset ×ˢ (S.fam X v (!true)).supp_finite.toFinset) ∪
      ((S.fam M v true).supp_finite.toFinset ×ˢ (S.fam M v (!true)).supp_finite.toFinset)
    rw [S.finrank_vsp_eq_sum_of_subset v true T Finset.subset_union_left,
      S.finrank_vsp_eq_sum_of_subset v true T Finset.subset_union_right]
    exact Finset.sum_congr rfl fun p _ ↦ hF v true p.1.1 p.2.1 p.1.2 p.2.2
  have hdim : finrank k X = finrank k M := by
    rw [finrank_eq_sum_vsp (D := D) X, finrank_eq_sum_vsp (D := D) M]
    exact Finset.sum_congr rfl fun v _ ↦ hvsp v
  -- surjectivity
  have hθc : ∀ (c : C) (y : (pc c).X), θ (Pi.single c y) = (pc c).θ y := by
    intro c y
    simp only [θ, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [Finset.sum_eq_single c]
    · show (pc c).θ (Pi.single (M := fun c : C ↦ (pc c).X) c y c) = _
      rw [Pi.single_eq_same]
    · intro c' _ hc'
      show (pc c').θ (Pi.single (M := fun c : C ↦ (pc c).X) c y c') = 0
      rw [Pi.single_eq_of_ne hc', map_zero]
    · simp
  have hsurj : Function.Surjective (θ.restrictScalars k) := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    have hv : ∀ v, D.vsp M v ≤ LinearMap.range (θ.restrictScalars k) := by
      intro v
      refine IFam.le_of_num_le (S.fam M v true) (S.fam M v (!true)) _ fun t t' ↦ ?_
      show S.pnum M v true t.1 t'.1 ≤ _ ⊔ S.pden M v true t.1 t'.1
      by_cases hle : S.pnum M v true t.1 t'.1 ≤ S.pden M v true t.1 t'.1
      · exact hle.trans le_sup_right
      · have hP : ((v, true, t.1, t'.1) : Pair D) ∈ NZ := ⟨t.2, t'.2, hle⟩
        have hc : Quotient.mk st ((v, true, t.1, t'.1) : Pair D) ∈ C :=
          Finset.mem_image_of_mem _ (hNZ.mem_toFinset.mpr hP)
        have hm := (hmem ⟨_, hc⟩ _ t.2 t'.2).mpr ⟨hP, rfl⟩
        refine ((pc ⟨_, hc⟩).hsurj _ hm).trans (sup_le_sup_right ?_ _)
        rintro _ ⟨y, rfl⟩
        exact ⟨Pi.single _ y, hθc _ y⟩
    intro x _
    rw [← one_smul B x, ← D.toPathData.sum_e, Finset.sum_smul]
    exact Submodule.sum_mem _ fun v _ ↦ hv v ⟨x, rfl⟩
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact ⟨C, inferInstance, inferInstance, pc, ⟨LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩⟩⟩

end BrickAccessibility
