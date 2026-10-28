module

public import BrickAccessibility.Classification.BandIndec

/-!
# Closed words give infinitely many indecomposables

A primitive band without zero paths gives the indecomposable, pairwise
non-isomorphic band modules `M(b, t)`, `t ∈ kˣ` (`not_isRepFinite_of_band`). Over a
gentle algebra, a closed word with all cyclic adjacent pairs allowed has a
primitive root which is such a band (`not_isRepFinite_of_closed`, Theorem 4.5,
band part).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B}

/-- Allowed pairs of consecutive letters alternate in sign. -/
theorem Signs.st_ne_en_of_allowed (S : D.Signs) {l l' : Letter D.Q} (h : D.AllowedPair l l')
    (hw : l.tgt = l'.src) : S.st l' ≠ S.en l := by
  obtain ⟨a, d⟩ := l
  obtain ⟨b, e⟩ := l'
  cases d <;> cases e <;> simp only [Letter.tgt, Letter.src, Bool.false_eq_true, if_false,
    if_true] at hw
  · -- `a⁻¹ b⁻¹`
    rw [allowedPair_ff] at h
    simp only [Signs.st_false, Signs.en_false]
    exact (S.hall b a ⟨hw, h⟩).symm
  · -- `a⁻¹ b`
    rw [allowedPair_ft] at h
    simp only [Signs.st_true, Signs.en_false]
    exact S.hσ b a (Ne.symm h) hw.symm
  · -- `a b⁻¹`
    rw [allowedPair_tf] at h
    simp only [Signs.st_false, Signs.en_true]
    exact S.hε b a (Ne.symm h) hw.symm
  · -- `a b`
    rw [allowedPair_tt] at h
    simp only [Signs.st_true, Signs.en_true]
    exact S.hall a b ⟨hw.symm, h⟩

end MonomialData

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)

include hA in
/-- Two consecutive moves along a band with allowed cyclic pairs compose to a nonzero path. -/
theorem pval_pair_ne (hall : ∀ q, D.AllowedPair (b.lt q) (b.lt (b.succ q))) {a a' : D.Q.A}
    {i i₁ i₂ : Fin b.n} (h1 : b.next a i = some i₁) (h2 : b.next a' i₁ = some i₂) :
    D.pval (D.Q.src a) [a, a'] ≠ 0 := by
  rcases (b.next_eq_some_iff S hA a i i₁).mp h1 with ⟨hl, rfl⟩ | ⟨hl, rfl⟩
  · rcases (b.next_eq_some_iff S hA a' _ i₂).mp h2 with ⟨hl', -⟩ | ⟨hl', -⟩
    · have := hall i
      rw [hl, hl', allowedPair_tt] at this
      exact this
    · rw [pred_succ, hl] at hl'
      simp at hl'
  · rcases (b.next_eq_some_iff S hA a' _ i₂).mp h2 with ⟨hl', -⟩ | ⟨hl', -⟩
    · rw [hl] at hl'; simp at hl'
    · have := hall (b.pred (b.pred i))
      rw [succ_pred, hl, hl', allowedPair_ff] at this
      exact this

include hA in
/-- Following arrows along a band gives a walk of direct letters with nonzero consecutive
pairs. -/
theorem follow_facts (hall : ∀ q, D.AllowedPair (b.lt q) (b.lt (b.succ q))) :
    ∀ (l : List D.Q.A) (i j : Fin b.n), b.followPos i l = some j →
      D.Q.IsWalk (b.vtx i) (l.map (·, true)) ∧
        ∀ (m : ℕ) (hm : m + 1 < l.length), D.pval (D.Q.src (l[m]'(by omega))) [l[m], l[m + 1]] ≠ 0 := by
  intro l
  induction l with
  | nil => intro _ _ _; exact ⟨trivial, fun m hm ↦ absurd hm (by simp)⟩
  | cons a l ih =>
      intro i j h
      simp only [followPos] at h
      cases hn : b.next a i with
      | none => rw [hn] at h; cases h
      | some i₁ =>
          rw [hn] at h
          obtain ⟨hw, hp⟩ := ih i₁ j h
          refine ⟨⟨by simp [Letter.src, b.next_src a i i₁ hn], ?_⟩, fun m hm ↦ ?_⟩
          · simpa [Letter.tgt, b.next_tgt a i i₁ hn] using hw
          · cases m with
            | zero =>
                cases l with
                | nil => simp at hm
                | cons a' l' =>
                    simp only [followPos] at h
                    cases hn' : b.next a' i₁ with
                    | none => rw [hn'] at h; cases h
                    | some i₂ => exact b.pval_pair_ne S hA hall hn hn'
            | succ m => exact hp m (by simp at hm; omega)

include hA in
/-- Over a gentle algebra, a band with allowed cyclic pairs has no zero paths. -/
theorem killsZero_of_allowed (hQ : D.IsQuadratic)
    (hall : ∀ q, D.AllowedPair (b.lt q) (b.lt (b.succ q))) : b.KillsZero := by
  intro x l hz i hi
  by_contra hf
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hf
  obtain ⟨hw, hp⟩ := b.follow_facts S hA hall l i j hj
  cases l with
  | nil => exact D.e_ne x hz
  | cons a l =>
      have hsrc : b.vtx i = D.Q.src a := hw.1.symm
      rw [← hi, hsrc] at hz
      rw [hsrc] at hw
      obtain ⟨m, hm, hfb⟩ := (hQ a l hw).mp hz
      exact hp m hm hfb.2

variable (hK : b.KillsZero)

include hA hK in
/-- **A primitive band without zero paths makes the algebra representation-infinite.** -/
theorem not_isRepFinite_of_band [Infinite k] [FiniteDimensional k B]
    (hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q) : ¬ IsRepFinite B := by
  classical
  rintro ⟨n, Ms, hMs⟩
  have hex : ∀ t : kˣ, ∃ i, Nonempty (b.BM S hA hK t ≃ₗ[B] Ms i) := fun t ↦ by
    haveI : Module.Finite B (b.BM S hA hK t) := Module.Finite.of_restrictScalars_finite k B _
    exact hMs _ (b.isIndecomposable S hA hK hprim t)
  choose idx hidx using hex
  have hinj : Function.Injective idx := by
    intro t t' e
    obtain ⟨e1⟩ := hidx t
    obtain ⟨e2⟩ := hidx t'
    rw [e] at e1
    exact b.eq_of_equiv S hA hK hprim (e1.trans e2.symm)
  have : Finite kˣ := Finite.of_injective idx hinj
  have : Finite {x : k // x ≠ 0} := Finite.of_equiv _ unitsEquivNeZero
  have : Function.Injective fun x : k ↦ if h : x = 0 then (none : Option {x : k // x ≠ 0})
      else some ⟨x, h⟩ := by
    intro x y e
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all
  have : Finite k := Finite.of_injective _ this
  exact not_finite k

/-- **The primitive band of a periodic half-word.** -/
theorem exists_prim_band {v : D.Q.V} {s : Bool} {f : ℕ → Letter D.Q} (hv : S.Valid v s (.inf f))
    {L : ℕ} (hL : 0 < L) (hperL : ∀ m, f (m + L) = f m) :
    ∃ (b : CWord D.Q) (_ : b.Alt S), (∀ p q, b.rightW p = b.rightW q → p = q) ∧
      (∀ q : Fin b.n, b.lt q = f q.val) ∧ (∀ q : Fin b.n, b.lt (b.succ q) = f (q.val + 1)) ∧
      b.n ≤ L := by
  classical
  have hex : ∃ q, 0 < q ∧ ∀ m, f (m + q) = f m := ⟨L, hL, hperL⟩
  set n := Nat.find hex
  have hn : 0 < n := (Nat.find_spec hex).1
  have hper : ∀ m, f (m + n) = f m := (Nat.find_spec hex).2
  have hmin : ∀ q, 0 < q → q < n → ¬ ∀ m, f (m + q) = f m :=
    fun q hq hlt hq' ↦ Nat.find_min hex hlt ⟨hq, hq'⟩
  obtain ⟨h0, -, hf⟩ := S.valid_inf_facts hv
  have hw : D.Q.IsWalk v (List.ofFn fun i : Fin n ↦ f i) := (hv n).1
  have hc : D.Q.wend v (List.ofFn fun i : Fin n ↦ f i) = v := by
    have h := hv (n + 1)
    rw [List.ofFn_succ_last] at h
    simp only [Fin.val_castSucc, Fin.val_last] at h
    have := (MonomialData.Signs.IsHW.last S h).1
    rw [← this, show n = 0 + n by omega, hper 0, h0]
  set b := ofPer v f n hn hw hc
  have hbn : b.n = n := ofPer_n
  have hR : ∀ p : Fin b.n, b.rightW p = fun t ↦ f (p.val + t) := fun p ↦
    funext fun t ↦ ofPer_lt_iter hper p t
  have hA : b.Alt S := by
    intro i
    have e1 : b.lt (b.succ i) = f (i.val + 1) := ofPer_lt_iter hper i 1
    rw [e1, ofPer_lt, (hf i.val).2]
    cases S.en (f i.val) <;> simp
  have hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q := by
    have key : ∀ p q : Fin b.n, p.val < q.val → b.rightW p = b.rightW q → False := by
      intro p q hpq hpq'
      rw [hR, hR] at hpq'
      have hq : q.val < n := by have := q.isLt; omega
      refine hmin (q.val - p.val) (by omega) (by omega) fun m ↦ ?_
      have h1 := congrFun hpq' (m + n * p.val - p.val)
      have hle : p.val ≤ n * p.val := Nat.le_mul_of_pos_left _ hn
      have e1 : p.val + (m + n * p.val - p.val) = m + n * p.val := by
        generalize n * p.val = X at hle ⊢; omega
      have e2 : q.val + (m + n * p.val - p.val) = m + (q.val - p.val) + n * p.val := by
        generalize n * p.val = X at hle ⊢; omega
      rw [e1, e2, MonomialData.per_add_mul hper, MonomialData.per_add_mul hper] at h1
      exact h1.symm
    intro p q h
    rcases lt_trichotomy p.val q.val with hlt | heq | hgt
    · exact (key p q hlt h).elim
    · exact Fin.ext heq
    · exact (key q p hgt h.symm).elim
  exact ⟨b, hA, hprim, fun q ↦ ofPer_lt q, fun q ↦ ofPer_lt_iter hper q 1,
    hbn ▸ Nat.find_min' hex ⟨hL, hperL⟩⟩

end CWord

namespace MonomialData

variable (D : MonomialData k B)

/-- **The band of an allowed closed word** over a gentle algebra. -/
theorem exists_band_of_closed (hD : D.IsGentle) (S : D.Signs)
    (x : D.Q.V) (ω : List (Letter D.Q)) (hne : ω ≠ []) (hwalk : D.Q.IsWalk x ω)
    (hend : D.Q.wend x ω = x) (hchain : ω.IsChain D.AllowedPair)
    (hcyc : D.AllowedPair (ω.getLast hne) (ω.head hne)) :
    ∃ (b : CWord D.Q) (hA : b.Alt S) (_ : b.KillsZero)
      (_ : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q), b.n ≤ ω.length ∧
      ∀ (q : Fin b.n) (hq : q.val < ω.length), b.lt q = ω[q.val] := by
  classical
  set L := ω.length
  have hL : 0 < L := List.length_pos_iff.mpr hne
  let w : Word D.Q := ⟨x, ω, hwalk⟩
  have hwL : w.len = L := rfl
  let f : ℕ → Letter D.Q := fun i ↦ ω[i % L]'(Nat.mod_lt _ hL)
  have hper : ∀ m, f (m + L) = f m := fun m ↦ by simp [f, Nat.add_mod_right]
  have hv0 : w.vtx ⟨0, by omega⟩ = x := rfl
  have hvL : w.vtx ⟨L, by omega⟩ = x := by
    show D.Q.wend x (ω.take L) = x
    rw [List.take_length]; exact hend
  have hconsec : ∀ i, (f i).tgt = (f (i + 1)).src ∧ D.AllowedPair (f i) (f (i + 1)) := by
    intro i
    have hi := Nat.mod_lt i hL
    by_cases h : i % L + 1 < L
    · have e : (i + 1) % L = i % L + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < L by omega), Nat.mod_eq_of_lt h]
      simp only [f, e]
      refine ⟨?_, (List.isChain_iff_getElem.mp hchain) (i % L) h⟩
      have h1 : (ω[i % L]).tgt = w.vtx ⟨i % L + 1, by omega⟩ := w.tgt_letter (i % L) (by omega)
      have h2 : (ω[i % L + 1]).src = w.vtx ⟨i % L + 1, by omega⟩ := w.src_letter _ (by omega)
      exact h1.trans h2.symm
    · have hi' : i % L = L - 1 := by omega
      have e : (i + 1) % L = 0 := by
        rw [← Nat.mod_add_mod, hi', show L - 1 + 1 = L by omega, Nat.mod_self]
      simp only [f, e, hi']
      refine ⟨?_, ?_⟩
      · have h1 : (ω[L - 1]).tgt = w.vtx ⟨L - 1 + 1, by omega⟩ := w.tgt_letter (L - 1) (by omega)
        have h2 : (ω[0]).src = w.vtx ⟨0, by omega⟩ := w.src_letter 0 (by omega)
        have e2 : (⟨L - 1 + 1, by omega⟩ : Fin (w.len + 1)) = ⟨L, by omega⟩ := Fin.ext (by simp; omega)
        rw [h1, h2, e2, hvL, hv0]
      · have := hcyc
        rwa [List.getLast_eq_getElem, List.head_eq_getElem] at this
  have h0 : (f 0).src = x := by
    simp only [f, Nat.zero_mod]
    rw [w.src_letter 0 hL]; rfl
  have hv : S.Valid x (S.st (f 0)) (.inf f) :=
    S.isHW_ofFn f h0 (fun i ↦ (hconsec i).1.symm) rfl
      (fun i ↦ S.st_ne_en_of_allowed (hconsec i).2 (hconsec i).1)
  obtain ⟨b, hA, hprim, hlt, hlts, hbL⟩ := CWord.exists_prim_band S hv hL hper
  have hall : ∀ q, D.AllowedPair (b.lt q) (b.lt (b.succ q)) := fun q ↦ by
    rw [hlt, hlts]; exact (hconsec q.val).2
  have hK := b.killsZero_of_allowed S hA hD.2.1 hall
  refine ⟨b, hA, hK, hprim, hbL, fun q hq ↦ ?_⟩
  rw [hlt]
  have hq' : q.val < L := hq
  simp only [f, Nat.mod_eq_of_lt hq']


/-- **Theorem 4.5, band part.** A closed word with all cyclic adjacent pairs allowed
over a gentle algebra makes the algebra representation-infinite. -/
theorem not_isRepFinite_of_closed [IsAlgClosed k] [FiniteDimensional k B] (hD : D.IsGentle)
    (x : D.Q.V) (ω : List (Letter D.Q)) (hne : ω ≠ []) (hwalk : D.Q.IsWalk x ω)
    (hend : D.Q.wend x ω = x) (hchain : ω.IsChain D.AllowedPair)
    (hcyc : D.AllowedPair (ω.getLast hne) (ω.head hne)) : ¬ IsRepFinite B := by
  obtain ⟨S⟩ := exists_signs (D := D) hD.1.2
  obtain ⟨b, hA, hK, hprim, -, -⟩ := D.exists_band_of_closed hD S x ω hne hwalk hend hchain hcyc
  exact b.not_isRepFinite_of_band S hA hK hprim

end MonomialData


end BrickAccessibility
