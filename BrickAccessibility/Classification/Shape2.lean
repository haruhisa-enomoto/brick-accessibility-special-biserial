module

public import BrickAccessibility.Classification.GoodSigns

/-!
# Band bricks of shape `P ω Q ω⁻¹`

Plamondon's second family: a cyclic word `P ++ ω ++ Q ++ ω⁻¹` where `P` and `Q`
are closed walks whose own junctions fail alternation, with the same direction
type at their ends. Positions with the same vertex are mirror positions across ω;
their halves agree along ω and first differ at the ends of `P` and of `Q`, and
the same direction type makes one of the two comparisons refute the plus-set
condition. Hence the band modules are bricks (`isBrick_shape2`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace CWord

variable {D : MonomialData k B} (b : CWord D.Q)

theorem rightW_val (q : Fin b.n) (t : ℕ) :
    b.rightW q t = b.letters[(q.val + t) % b.n]'(Nat.mod_lt _ b.n_pos) := by
  simp only [rightW, lt]
  congr 1
  rw [iter_succ_val]

theorem leftW_val (q : Fin b.n) (t : ℕ) (ht : t < b.n) :
    b.leftW q t = (b.letters[(q.val + b.n - 1 - t) % b.n]'(Nat.mod_lt _ b.n_pos)).inv := by
  simp only [leftW, lt]
  congr 2
  have hq := q.isLt
  have e : b.pred^[t + 1] q = ⟨(q.val + b.n - 1 - t) % b.n, Nat.mod_lt _ b.n_pos⟩ := by
    refine b.eq_of_add_mod (m := t + 1) ?_
    rw [iter_pred_val_mod]
    show q.val = ((q.val + b.n - 1 - t) % b.n + (t + 1)) % b.n
    rw [Nat.mod_add_mod, show q.val + b.n - 1 - t + (t + 1) = q.val + b.n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  rw [e]

/-- A first difference of direction refutes the plus-set condition. -/
theorem code_lt_of_diff {f g : ℕ → Letter D.Q} (K : ℕ) (hfg : ∀ t < K, f t = g t)
    (hf : (f K).2 = false) (hg : (g K).2 = true) :
    toLex (HWord.inf f).code < toLex (HWord.inf g).code := by
  refine ⟨K, fun j hj ↦ ?_, ?_⟩
  · show (HWord.inf f).code j = (HWord.inf g).code j
    simp only [HWord.code, hfg j hj]
  · show (HWord.inf f).code K < (HWord.inf g).code K
    simp [HWord.code, hf, hg]

section Shape

variable {P ω Q : List (Letter D.Q)} (hc : b.letters = P ++ ω ++ Q ++ invLetters ω)
include hc

theorem shape_n : b.n = P.length + ω.length + Q.length + ω.length := by
  show b.letters.length = _
  rw [hc]; simp [invLetters]; omega

theorem shape_len : b.letters.length = P.length + ω.length + Q.length + ω.length := b.shape_n hc

theorem shape_P (j : ℕ) (hj : j < P.length) :
    b.letters[j]'(by rw [b.shape_len hc]; omega) = P[j] := by
  rw [List.getElem_of_eq hc]
  simp [List.getElem_append, hj, show j < P.length + ω.length by omega,
    show j < P.length + ω.length + Q.length by omega]

theorem shape_ω (j : ℕ) (hj : j < ω.length) :
    b.letters[P.length + j]'(by rw [b.shape_len hc]; omega) = ω[j] := by
  rw [List.getElem_of_eq hc]
  simp [List.getElem_append, hj, show P.length + j < P.length + ω.length + Q.length by omega]

theorem shape_Q (j : ℕ) (hj : j < Q.length) :
    b.letters[P.length + ω.length + j]'(by rw [b.shape_len hc]; omega) = Q[j] := by
  rw [List.getElem_of_eq hc, List.getElem_append_left (by simp; omega),
    List.getElem_append_right (by simp)]
  simp only [List.length_append, show P.length + ω.length + j - (P.length + ω.length) = j by omega]

theorem shape_I (j : ℕ) (hj : j < ω.length) :
    b.letters[P.length + ω.length + Q.length + j]'(by rw [b.shape_len hc]; omega) =
      (ω[ω.length - 1 - j]).inv := by
  rw [List.getElem_of_eq hc, List.getElem_append_right (by simp; omega)]
  simp only [List.length_append,
    show P.length + ω.length + Q.length + j - (P.length + ω.length + Q.length) = j by omega]
  simp [invLetters, List.getElem_reverse]

omit hc in
theorem getL (j j' : ℕ) (hj : j < b.n) (h : j = j') :
    b.letters[j]'hj = b.letters[j']'(h ▸ hj) := by subst h; rfl

omit hc in
theorem mod_mirror (i t : ℕ) (h : i + t + 1 ≤ b.n) :
    ((b.n - i) % b.n + b.n - 1 - t) % b.n = b.n - i - 1 - t := by
  have hn := b.n_pos
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [Nat.sub_zero, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (show b.n - i < b.n by omega),
      show b.n - i + b.n - 1 - t = (b.n - i - 1 - t) + b.n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

variable (hP : P ≠ []) (hQ : Q ≠ [])
include hP hQ

/-- The forward half from `|P| + i` and the backward half from its mirror. -/
theorem shape_A1 (i : ℕ) (hi : i ≤ ω.length) :
    let a : Fin b.n := ⟨P.length + i, by rw [b.shape_n hc]; have := List.length_pos_iff.mpr hQ; omega⟩
    let a' : Fin b.n := ⟨(b.n - i) % b.n, Nat.mod_lt _ b.n_pos⟩
    (∀ t < ω.length - i, b.rightW a t = b.leftW a' t) ∧ b.rightW a (ω.length - i) = Q.head hQ ∧
      b.leftW a' (ω.length - i) = (Q.getLast hQ).inv := by
  intro a a'
  have hn := b.shape_n hc
  have hP0 := List.length_pos_iff.mpr hP
  have hQ0 := List.length_pos_iff.mpr hQ
  have hR : ∀ t ≤ ω.length - i, (a.val + t) % b.n = P.length + i + t := fun t ht ↦
    Nat.mod_eq_of_lt (by simp only [a]; omega)
  have hLv : ∀ t ≤ ω.length - i, (a'.val + b.n - 1 - t) % b.n =
      P.length + ω.length + Q.length + (ω.length - i - 1 - t) ∨ t = ω.length - i := by
    intro t ht
    rcases Nat.lt_or_ge t (ω.length - i) with h | h
    · left
      simp only [a']
      rw [b.mod_mirror i t (by omega)]; omega
    · right; omega
  refine ⟨fun t ht ↦ ?_, ?_, ?_⟩
  · rw [b.rightW_val, b.leftW_val _ _ (by omega)]
    have e1 := hR t ht.le
    rcases hLv t ht.le with e2 | e2
    · rw [b.getL _ (P.length + (i + t)) _ (by rw [e1]; omega),
        b.getL _ (P.length + ω.length + Q.length + (ω.length - i - 1 - t)) _ e2,
        b.shape_ω hc _ (by omega), b.shape_I hc _ (by omega), Letter.inv_inv']
      congr 1; omega
    · omega
  · rw [b.rightW_val, b.getL _ (P.length + ω.length + 0) _ (by rw [hR _ le_rfl]; omega),
      b.shape_Q hc 0 hQ0, List.head_eq_getElem]
  · rw [b.leftW_val _ _ (by omega)]
    have e2 : (a'.val + b.n - 1 - (ω.length - i)) % b.n = P.length + ω.length + (Q.length - 1) := by
      simp only [a']
      rw [b.mod_mirror i _ (by omega)]; omega
    rw [b.getL _ _ _ e2, b.shape_Q hc _ (by omega), List.getLast_eq_getElem]

/-- The backward half from `|P| + i` and the forward half from its mirror. -/
theorem shape_A2 (i : ℕ) (hi : i ≤ ω.length) :
    let a : Fin b.n := ⟨P.length + i, by rw [b.shape_n hc]; have := List.length_pos_iff.mpr hQ; omega⟩
    let a' : Fin b.n := ⟨(b.n - i) % b.n, Nat.mod_lt _ b.n_pos⟩
    (∀ t < i, b.leftW a t = b.rightW a' t) ∧ b.leftW a i = (P.getLast hP).inv ∧
      b.rightW a' i = P.head hP := by
  intro a a'
  have hn := b.shape_n hc
  have hP0 := List.length_pos_iff.mpr hP
  have hQ0 := List.length_pos_iff.mpr hQ
  have hLa : ∀ t ≤ i, (a.val + b.n - 1 - t) % b.n = P.length + i - 1 - t := fun t ht ↦ by
    simp only [a]
    rw [show P.length + i + b.n - 1 - t = (P.length + i - 1 - t) + b.n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hRa : ∀ t < i, (a'.val + t) % b.n = P.length + ω.length + Q.length + (ω.length - i + t) :=
    fun t ht ↦ by
      simp only [a']
      rw [Nat.mod_eq_of_lt (show b.n - i < b.n by omega), Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨fun t ht ↦ ?_, ?_, ?_⟩
  · rw [b.leftW_val _ _ (by omega), b.rightW_val,
      b.getL _ (P.length + (i - 1 - t)) _ (by rw [hLa t ht.le]; omega),
      b.getL _ (P.length + ω.length + Q.length + (ω.length - i + t)) _ (hRa t ht),
      b.shape_ω hc _ (by omega), b.shape_I hc _ (by omega)]
    congr 2; omega
  · rw [b.leftW_val _ _ (by omega), b.getL _ (P.length - 1) _ (by rw [hLa i le_rfl]; omega),
      b.shape_P hc _ (by omega), List.getLast_eq_getElem]
  · rw [b.rightW_val]
    have e : (a'.val + i) % b.n = 0 := by
      simp only [a']
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0; simp
      · rw [Nat.mod_eq_of_lt (show b.n - i < b.n by omega), show b.n - i + i = b.n by omega,
          Nat.mod_self]
    rw [b.getL _ 0 _ e, b.shape_P hc 0 hP0, List.head_eq_getElem]

end Shape


section Coincide

/-- The vertices along ω, ending with the start of `Q`. -/
def ωv {Q : FinQuiver} (ω R : List (Letter Q)) (hR : R ≠ []) (t : ℕ) : Q.V :=
  if h : t < ω.length then (ω[t]).src else (R.head hR).src

variable {P ω Q : List (Letter D.Q)} (hc : b.letters = P ++ ω ++ Q ++ invLetters ω)
  (hP : P ≠ []) (hQ : Q ≠ [])
include hc hP hQ

theorem vtx_P (s : ℕ) (hs : s < P.length) :
    b.vtx ⟨s, by have := b.shape_n hc; omega⟩ = (P[s]).src := by
  show (b.letters[s]'(by have := b.shape_len hc; omega)).src = _
  rw [b.shape_P hc s hs]

theorem vtx_ω (t : ℕ) (ht : t < ω.length) :
    b.vtx ⟨P.length + t, by have := b.shape_n hc; omega⟩ = ωv ω Q hQ t := by
  show (b.letters[P.length + t]'(by have := b.shape_len hc; omega)).src = _
  rw [b.shape_ω hc t ht, ωv, dif_pos ht]

theorem vtx_Q (s : ℕ) (hs : s < Q.length) :
    b.vtx ⟨P.length + ω.length + s, by have := b.shape_n hc; omega⟩ = (Q[s]).src := by
  show (b.letters[P.length + ω.length + s]'(by have := b.shape_len hc; omega)).src = _
  rw [b.shape_Q hc s hs]

theorem tgt_ω (t : ℕ) (ht : t < ω.length) : (ω[t]).tgt = ωv ω Q hQ (t + 1) := by
  have h := b.lt_tgt ⟨P.length + t, by have := b.shape_n hc; omega⟩
  have e1 : b.lt ⟨P.length + t, by have := b.shape_n hc; omega⟩ = ω[t] := b.shape_ω hc t ht
  rw [e1] at h
  rw [h]
  have hs : (b.succ ⟨P.length + t, by have := b.shape_n hc; omega⟩).val = P.length + t + 1 :=
    b.succ_val_of_lt _ (by have := b.shape_n hc; have := List.length_pos_iff.mpr hQ; simp; omega)
  by_cases h1 : t + 1 < ω.length
  · have e : b.succ ⟨P.length + t, by have := b.shape_n hc; omega⟩ =
        ⟨P.length + (t + 1), by have := b.shape_n hc; omega⟩ := Fin.ext (by rw [hs]; simp; omega)
    rw [e, b.vtx_ω hc hP hQ _ h1]
  · have hQ0 := List.length_pos_iff.mpr hQ
    have e : b.succ ⟨P.length + t, by have := b.shape_n hc; omega⟩ =
        ⟨P.length + ω.length + 0, by have := b.shape_n hc; omega⟩ := Fin.ext (by rw [hs]; simp; omega)
    rw [e, b.vtx_Q hc hP hQ 0 hQ0, ωv, dif_neg h1, List.head_eq_getElem]

theorem vtx_I (r : ℕ) (hr : r < ω.length) :
    b.vtx ⟨P.length + ω.length + Q.length + r, by have := b.shape_n hc; omega⟩ =
      ωv ω Q hQ (ω.length - r) := by
  show (b.letters[P.length + ω.length + Q.length + r]'(by have := b.shape_len hc; omega)).src = _
  rw [b.shape_I hc r hr, Letter.src_inv, b.tgt_ω hc hP hQ _ (by omega)]
  congr 1; omega

/-- **Vertex coincidences** of a shape `P ω Q ω⁻¹` from simple vertex sequences. -/
theorem shape_coincide
    (hPi : ∀ s s' (hs : s < P.length) (hs' : s' < P.length), (P[s]).src = (P[s']).src → s = s')
    (hQi : ∀ s s' (hs : s < Q.length) (hs' : s' < Q.length), (Q[s]).src = (Q[s']).src → s = s')
    (hωi : ∀ t t', t ≤ ω.length → t' ≤ ω.length → ωv ω Q hQ t = ωv ω Q hQ t' → t = t')
    (hPω : ∀ s t (hs : s < P.length), t ≤ ω.length → (P[s]).src = ωv ω Q hQ t → s = 0 ∧ t = 0)
    (hQω : ∀ s t (hs : s < Q.length), t ≤ ω.length → (Q[s]).src = ωv ω Q hQ t →
      s = 0 ∧ t = ω.length)
    (hPQ : ∀ s s' (hs : s < P.length) (hs' : s' < Q.length), (P[s]).src = (Q[s']).src →
      ω.length = 0 ∧ s = 0 ∧ s' = 0) :
    ∀ p q : Fin b.n, b.vtx p = b.vtx q → p = q ∨
      (∃ i ≤ ω.length, q.val = P.length + i ∧ p.val = (b.n - i) % b.n) ∨
      (∃ i ≤ ω.length, p.val = P.length + i ∧ q.val = (b.n - i) % b.n) := by
  have hn := b.shape_n hc
  have hQ0 := List.length_pos_iff.mpr hQ
  -- the vertex of a position, by regions
  have key : ∀ p : Fin b.n,
      (∃ s, ∃ hs : s < P.length, p.val = s ∧ b.vtx p = (P[s]).src) ∨
      (∃ t < ω.length, p.val = P.length + t ∧ b.vtx p = ωv ω Q hQ t) ∨
      (∃ s, ∃ hs : s < Q.length, p.val = P.length + ω.length + s ∧ b.vtx p = (Q[s]).src) ∨
      (∃ r < ω.length, p.val = P.length + ω.length + Q.length + r ∧
        b.vtx p = ωv ω Q hQ (ω.length - r)) := by
    intro p
    have hp := p.isLt
    by_cases h1 : p.val < P.length
    · left; exact ⟨p.val, h1, rfl, b.vtx_P hc hP hQ p.val h1⟩
    by_cases h2 : p.val < P.length + ω.length
    · right; left
      refine ⟨p.val - P.length, by omega, by omega, ?_⟩
      rw [← b.vtx_ω hc hP hQ _ (by omega)]
      congr 1; exact Fin.ext (by simp; omega)
    by_cases h3 : p.val < P.length + ω.length + Q.length
    · right; right; left
      refine ⟨p.val - P.length - ω.length, by omega, by omega, ?_⟩
      rw [← b.vtx_Q hc hP hQ _ (by omega)]
      congr 1; exact Fin.ext (by simp; omega)
    · right; right; right
      refine ⟨p.val - P.length - ω.length - Q.length, by omega, by omega, ?_⟩
      rw [← b.vtx_I hc hP hQ _ (by omega)]
      congr 1; exact Fin.ext (by simp; omega)
  have hωQ0 : ωv ω Q hQ ω.length = (Q[0]).src := by
    rw [ωv, dif_neg (lt_irrefl _), List.head_eq_getElem]
  intro p q hv
  rcases key p with ⟨s, hs, hp, ep⟩ | ⟨t, ht, hp, ep⟩ | ⟨s, hs, hp, ep⟩ | ⟨r, hr, hp, ep⟩ <;>
  rcases key q with ⟨s', hs', hq, eq⟩ | ⟨t', ht', hq, eq⟩ | ⟨s', hs', hq, eq⟩ | ⟨r', hr', hq, eq⟩ <;>
  rw [ep, eq] at hv
  -- P, P
  · left; exact Fin.ext (by rw [hp, hq]; exact hPi s s' hs hs' hv)
  -- P, ω
  · obtain ⟨rfl, rfl⟩ := hPω s t' hs ht'.le hv
    right; left; exact ⟨0, by omega, by rw [hq], by rw [hp]; simp⟩
  -- P, Q
  · obtain ⟨hm, rfl, rfl⟩ := hPQ s s' hs hs' hv
    right; left; exact ⟨0, by omega, by rw [hq]; omega, by rw [hp]; simp⟩
  -- P, I
  · obtain ⟨-, h⟩ := hPω s _ hs (by omega) hv; omega
  -- ω, P
  · obtain ⟨rfl, rfl⟩ := hPω s' t hs' ht.le hv.symm
    right; right; exact ⟨0, by omega, by rw [hp], by rw [hq]; simp⟩
  -- ω, ω
  · left; exact Fin.ext (by rw [hp, hq, hωi t t' ht.le ht'.le hv])
  -- ω, Q
  · obtain ⟨-, h⟩ := hQω s' t hs' ht.le hv.symm; omega
  -- ω, I
  · have := hωi _ _ ht.le (by omega) hv
    right; right; exact ⟨t, ht.le, hp, by rw [hq, Nat.mod_eq_of_lt (by omega)]; omega⟩
  -- Q, P
  · obtain ⟨hm, rfl, rfl⟩ := hPQ s' s hs' hs hv.symm
    right; right; exact ⟨0, by omega, by rw [hp]; omega, by rw [hq]; simp⟩
  -- Q, ω
  · obtain ⟨-, h⟩ := hQω s t' hs ht'.le hv; omega
  -- Q, Q
  · left; exact Fin.ext (by rw [hp, hq, hQi s s' hs hs' hv])
  -- Q, I
  · obtain ⟨rfl, h⟩ := hQω s _ hs (by omega) hv
    right; right
    exact ⟨ω.length, le_rfl, by rw [hp]; omega, by rw [hq, Nat.mod_eq_of_lt (by omega)]; omega⟩
  -- I, P
  · obtain ⟨-, h⟩ := hPω s' _ hs' (by omega) hv.symm; omega
  -- I, ω
  · have := hωi _ _ (by omega) ht'.le hv
    right; left; exact ⟨t', ht'.le, hq, by rw [hp, Nat.mod_eq_of_lt (by omega)]; omega⟩
  -- I, Q
  · obtain ⟨rfl, h⟩ := hQω s' _ hs' (by omega) hv.symm
    right; left
    exact ⟨ω.length, le_rfl, by rw [hq]; omega, by rw [hp, Nat.mod_eq_of_lt (by omega)]; omega⟩
  -- I, I
  · left; exact Fin.ext (by have := hωi _ _ (by omega) (by omega) hv; rw [hp, hq]; omega)

end Coincide

section Brick

variable (S : D.Signs) (hA : b.Alt S) (hK : b.KillsZero)
variable {P ω Q : List (Letter D.Q)} (hc : b.letters = P ++ ω ++ Q ++ invLetters ω)
  (hP : P ≠ []) (hQ : Q ≠ [])

include hA hc hK in
/-- The plus-set condition for shape `P ω Q ω⁻¹`. -/
theorem shape2_hN (hPj : S.st (P.head hP) = S.en (P.getLast hP))
    (hPt : (P.getLast hP).2 = (P.head hP).2) (hQt : (Q.getLast hQ).2 = (Q.head hQ).2)
    (hPQ : (P.head hP).2 = (Q.head hQ).2)
    (hH : ∀ p q : Fin b.n, b.vtx p = b.vtx q → p = q ∨
      (∃ i ≤ ω.length, q.val = P.length + i ∧ p.val = (b.n - i) % b.n) ∨
      (∃ i ≤ ω.length, p.val = P.length + i ∧ q.val = (b.n - i) % b.n)) (t : kˣ) :
    ∀ p q : Fin b.n, p ≠ q →
      ¬ ((b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (S.st (b.lt q)) (.inf (b.rightW q)) p ∧
        (b.blockQuiver S hA k (tw t)).plusSet S (b.vtx q) (!S.st (b.lt q)) (.inf (b.leftW q)) p) := by
  have hQ0 := List.length_pos_iff.mpr hQ
  set C := b.blockQuiver S hA k (tw t)
  set hC := b.blockQuiver_kills S hA hK k (tw t)
  -- the pair at mirror positions
  have pair : ∀ (i : ℕ) (hi : i ≤ ω.length),
      let a : Fin b.n := ⟨P.length + i, by rw [b.shape_n hc]; omega⟩
      let a' : Fin b.n := ⟨(b.n - i) % b.n, Nat.mod_lt _ b.n_pos⟩
      b.vtx a' = b.vtx a →
      ¬ (C.plusSet S (b.vtx a) (S.st (b.lt a)) (.inf (b.rightW a)) a' ∧
          C.plusSet S (b.vtx a) (!S.st (b.lt a)) (.inf (b.leftW a)) a') ∧
      ¬ (C.plusSet S (b.vtx a') (S.st (b.lt a')) (.inf (b.rightW a')) a ∧
          C.plusSet S (b.vtx a') (!S.st (b.lt a')) (.inf (b.leftW a')) a) := by
    intro i hi a a' hv
    obtain ⟨h1, h1q, h1q'⟩ := b.shape_A1 hc hP hQ i hi
    obtain ⟨h2, h2p, h2p'⟩ := b.shape_A2 hc hP hQ i hi
    -- signs
    have hsign : S.st (b.lt a') = !S.st (b.lt a) := by
      have e0 : S.st (b.rightW a' 0) = S.st (b.leftW a 0) := by
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · have e1 : b.rightW a' 0 = P.head hP := by convert h2p' using 2; omega
          have e2 : b.leftW a 0 = (P.getLast hP).inv := by convert h2p using 2; omega
          rw [e1, e2, Signs.st_inv, hPj]
        · rw [h2 0 hi0]
      have e1 : b.rightW a' 0 = b.lt a' := rfl
      have e2 : S.st (b.leftW a 0) = !S.st (b.lt a) := by
        show S.st (b.lt (b.pred a)).inv = _
        rw [Signs.st_inv, b.en_pred S hA]
      rw [← e1, e0, e2]
    have hb1 : b.bhalf S a' (!S.st (b.lt a)) = .inf (b.rightW a') := by
      rw [← hsign, bhalf_self]
    have hb2 : b.bhalf S a' (S.st (b.lt a)) = .inf (b.leftW a') := by
      rw [show S.st (b.lt a) = !S.st (b.lt a') by rw [hsign]; simp, bhalf_not]
    have hb3 : b.bhalf S a (S.st (b.lt a')) = .inf (b.leftW a) := by rw [hsign, bhalf_not]
    have hb4 : b.bhalf S a (!S.st (b.lt a')) = .inf (b.rightW a) := by
      rw [hsign]; simp only [Bool.not_not]; rw [bhalf_self]
    have hlast : ∀ l : Letter D.Q, l.inv.2 = !l.2 := fun l ↦ rfl
    constructor
    · rintro ⟨hR, hL⟩
      by_cases hdir : (P.head hP).2 = true
      · apply b.not_plusSet_of_lt S hA (tw t) hC hv (!S.st (b.lt a)) ?_ (by rw [bhalf_not]; exact hL)
        rw [bhalf_not, hb1]
        exact code_lt_of_diff i h2 (by rw [h2p, hlast, hPt, hdir]; rfl) (by rw [h2p', hdir])
      · apply b.not_plusSet_of_lt S hA (tw t) hC hv (S.st (b.lt a)) ?_ (by rw [bhalf_self]; exact hR)
        rw [bhalf_self, hb2]
        refine code_lt_of_diff (ω.length - i) h1 (by rw [h1q, ← hPQ]; simpa using hdir) ?_
        rw [h1q', hlast, hQt, ← hPQ]; simpa using hdir
    · rintro ⟨hR, hL⟩
      by_cases hdir : (P.head hP).2 = true
      · apply b.not_plusSet_of_lt S hA (tw t) hC hv.symm (!S.st (b.lt a')) ?_
          (by rw [bhalf_not]; exact hL)
        rw [bhalf_not, hb4]
        refine code_lt_of_diff (ω.length - i) (fun t ht ↦ (h1 t ht).symm) ?_ ?_
        · rw [h1q', hlast, hQt, ← hPQ, hdir]; rfl
        · rw [h1q, ← hPQ, hdir]
      · apply b.not_plusSet_of_lt S hA (tw t) hC hv.symm (S.st (b.lt a')) ?_
          (by rw [bhalf_self]; exact hR)
        rw [bhalf_self, hb3]
        refine code_lt_of_diff i (fun t ht ↦ (h2 t ht).symm) (by rw [h2p']; simpa using hdir) ?_
        rw [h2p, hlast, hPt]; simpa using hdir
  intro p q hpq hboth
  have hv : b.vtx p = b.vtx q := hboth.1 0
  rcases hH p q hv with h | ⟨i, hi, hq, hp⟩ | ⟨i, hi, hp, hq⟩
  · exact hpq h
  · have eq : q = ⟨P.length + i, by rw [b.shape_n hc]; omega⟩ := Fin.ext hq
    have ep : p = ⟨(b.n - i) % b.n, Nat.mod_lt _ b.n_pos⟩ := Fin.ext hp
    rw [eq, ep] at hboth hv
    exact (pair i hi hv).1 hboth
  · have ep : p = ⟨P.length + i, by rw [b.shape_n hc]; omega⟩ := Fin.ext hp
    have eq : q = ⟨(b.n - i) % b.n, Nat.mod_lt _ b.n_pos⟩ := Fin.ext hq
    rw [eq, ep] at hboth hv
    exact (pair i hi hv.symm).2 hboth

include hA hc in
/-- **Band bricks of shape `P ω Q ω⁻¹`.** -/
theorem isBrick_shape2 (hPj : S.st (P.head hP) = S.en (P.getLast hP))
    (hPt : (P.getLast hP).2 = (P.head hP).2) (hQt : (Q.getLast hQ).2 = (Q.head hQ).2)
    (hPQ : (P.head hP).2 = (Q.head hQ).2)
    (hH : ∀ p q : Fin b.n, b.vtx p = b.vtx q → p = q ∨
      (∃ i ≤ ω.length, q.val = P.length + i ∧ p.val = (b.n - i) % b.n) ∨
      (∃ i ≤ ω.length, p.val = P.length + i ∧ q.val = (b.n - i) % b.n)) (t : kˣ) :
    IsBrick B (b.BM S hA hK t) :=
  b.isBrick_of_plusSets' S hA hK t (b.shape2_hN S hA hK hc hP hQ hPj hPt hQt hPQ hH t)

end Brick

end CWord

end BrickAccessibility
