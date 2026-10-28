module

public import BrickAccessibility.Classification.Shape2

/-!
# Plamondon's selection of a brick band

Over a gentle algebra with good signs, an alternating cyclic word of minimal length
either passes through distinct vertices, or yields a cyclic word of the shape
`P ω Q ω⁻¹` of `Shape2`; in both cases the band modules are bricks
(Plamondon, *τ-tilting finite gentle algebras are representation-finite*, §4).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module MonomialData

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace CWord

variable {D : MonomialData k B}

/-- The cyclic word on the first `L` values of a letter function. -/
def mkC (g : ℕ → Letter D.Q) (L : ℕ) (hL : 0 < L)
    (hw : ∀ t, t + 1 < L → (g t).tgt = (g (t + 1)).src) (hc : (g (L - 1)).tgt = (g 0).src) :
    CWord D.Q where
  start := (g 0).src
  letters := List.ofFn fun i : Fin L ↦ g i
  ne := by rw [Ne, List.ofFn_eq_nil_iff]; omega
  walk := by
    have key : ∀ m s, s + m ≤ L → D.Q.IsWalk (g s).src (List.ofFn fun i : Fin m ↦ g (s + i)) ∧
        (0 < m → D.Q.wend (g s).src (List.ofFn fun i : Fin m ↦ g (s + i)) = (g (s + m - 1)).tgt) := by
      intro m
      induction m with
      | zero => intro s _; exact ⟨trivial, fun h ↦ absurd h (lt_irrefl _)⟩
      | succ m ih =>
          intro s hs
          rw [List.ofFn_succ]
          obtain ⟨h1, h2⟩ := ih (s + 1) (by omega)
          simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
          have e : (fun i : Fin m ↦ g (s + (i.val + 1))) = fun i : Fin m ↦ g (s + 1 + i.val) := by
            funext i; congr 1; omega
          rw [e]
          refine ⟨⟨rfl, ?_⟩, fun _ ↦ ?_⟩
          · rcases Nat.eq_zero_or_pos m with hm | hm
            · subst hm; trivial
            · rw [show (g s).tgt = (g (s + 1)).src from hw s (by omega)]; exact h1
          · rcases Nat.eq_zero_or_pos m with hm | hm
            · subst hm; simp [Statement.FinQuiver.wend]
            · show D.Q.wend (g s).tgt _ = _
              rw [show (g s).tgt = (g (s + 1)).src from hw s (by omega), h2 hm]
              congr 2; omega
    simpa using (key L 0 (by omega)).1
  closed := by
    have key : ∀ m s, s + m ≤ L → 0 < m →
        D.Q.wend (g s).src (List.ofFn fun i : Fin m ↦ g (s + i)) = (g (s + m - 1)).tgt := by
      intro m
      induction m with
      | zero => intro _ _ h; omega
      | succ m ih =>
          intro s hs _
          rw [List.ofFn_succ]
          simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
          rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm; simp [Statement.FinQuiver.wend]
          · show D.Q.wend (g s).tgt _ = _
            have e : (fun i : Fin m ↦ g (s + (i.val + 1))) = fun i : Fin m ↦ g (s + 1 + i.val) := by
              funext i; congr 1; omega
            rw [e, show (g s).tgt = (g (s + 1)).src from hw s (by omega), ih (s + 1) (by omega) hm]
            congr 2; omega
    have := key L 0 (by omega) hL
    simp only [Nat.zero_add] at this
    rw [this, hc]

section
variable (g : ℕ → Letter D.Q) (L : ℕ) (hL : 0 < L)
    (hw : ∀ t, t + 1 < L → (g t).tgt = (g (t + 1)).src) (hc : (g (L - 1)).tgt = (g 0).src)

theorem mkC_n : (mkC g L hL hw hc).n = L := List.length_ofFn

theorem mkC_lt (i : Fin (mkC g L hL hw hc).n) : (mkC g L hL hw hc).lt i = g i.val := by
  simp [lt, mkC]

/-- Alternation of `mkC` from internal alternation and the junction. -/
theorem mkC_alt (S : D.Signs) (hint : ∀ t, t + 1 < L → S.st (g (t + 1)) ≠ S.en (g t))
    (hj : S.st (g 0) ≠ S.en (g (L - 1))) : (mkC g L hL hw hc).Alt S := by
  intro i
  have hn := mkC_n g L hL hw hc
  have hi := i.isLt
  rw [mkC_lt, mkC_lt]
  by_cases h : i.val + 1 < (mkC g L hL hw hc).n
  · rw [succ_val_of_lt _ _ h]; exact hint _ (by omega)
  · rw [succ_val_of_last _ _ (by omega), show i.val = L - 1 by omega]; exact hj
end

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
  (hmin : ∀ c : CWord D.Q, c.Alt S → b.n ≤ c.n)

/-- The periodic letter sequence of `b`. -/
def fl (t : ℕ) : Letter D.Q := b.lt (b.succ^[t] b.first)

/-- The periodic vertex sequence of `b`. -/
def vt (t : ℕ) : D.Q.V := (b.fl t).src

theorem fl_walk (t : ℕ) : (b.fl t).tgt = (b.fl (t + 1)).src := by
  simp only [fl]
  rw [b.lt_tgt, Function.iterate_succ_apply']
  rfl

include hA in
theorem fl_alt (t : ℕ) : S.st (b.fl (t + 1)) ≠ S.en (b.fl t) := by
  simp only [fl]
  rw [Function.iterate_succ_apply']
  exact hA _

theorem fl_per (t : ℕ) : b.fl (t + b.n) = b.fl t := by
  simp only [fl]
  rw [Function.iterate_add_apply, b.iter_succ_n]

theorem fl_val (t : ℕ) : b.fl t = b.lt ⟨t % b.n, Nat.mod_lt _ b.n_pos⟩ := by
  simp only [fl]
  congr 1
  exact Fin.ext (by rw [iter_succ_val]; simp [first])

include hmin in
/-- No alternating cyclic word is shorter than `b`. -/
theorem shorter_false (g : ℕ → Letter D.Q) (L : ℕ) (hL : 0 < L) (hLn : L < b.n)
    (hw : ∀ t, t + 1 < L → (g t).tgt = (g (t + 1)).src) (hc : (g (L - 1)).tgt = (g 0).src)
    (hint : ∀ t, t + 1 < L → S.st (g (t + 1)) ≠ S.en (g t))
    (hj : S.st (g 0) ≠ S.en (g (L - 1))) : False := by
  have := hmin (mkC g L hL hw hc) (mkC_alt g L hL hw hc S hint hj)
  rw [mkC_n] at this
  omega

include hA hmin in
/-- **Junction failure**: a shorter closed sub-walk does not alternate at its junction. -/
theorem junction (i L : ℕ) (hL : 0 < L) (hLn : L < b.n) (hv : b.vt i = b.vt (i + L)) :
    S.st (b.fl i) = S.en (b.fl (i + L - 1)) := by
  by_contra h
  refine b.shorter_false S hmin (fun t ↦ b.fl (i + t)) L hL hLn (fun t _ ↦ by
    rw [b.fl_walk, Nat.add_assoc]) ?_ (fun t _ ↦ by
    have := b.fl_alt S hA (i + t); rwa [Nat.add_assoc] at this) ?_
  · simp only [Nat.add_zero]
    rw [b.fl_walk, show i + (L - 1) + 1 = i + L by omega]
    exact hv.symm
  · simpa [show i + (L - 1) = i + L - 1 by omega] using h

include hA hmin in
/-- **At most two visits** to a vertex in a period. -/
theorem two_visits {i j l : ℕ} (hij : i < j) (hjl : j < l) (hl : l < i + b.n)
    (h1 : b.vt i = b.vt j) (h2 : b.vt j = b.vt l) : False := by
  have e1 := b.junction S hA hmin i (j - i) (by omega) (by omega)
    (by rw [show i + (j - i) = j by omega]; exact h1)
  have e2 := b.junction S hA hmin j (l - j) (by omega) (by omega)
    (by rw [show j + (l - j) = l by omega]; exact h2)
  have e3 := b.junction S hA hmin i (l - i) (by omega) (by omega)
    (by rw [show i + (l - i) = l by omega]; exact h1.trans h2)
  rw [show i + (j - i) - 1 = j - 1 by omega] at e1
  rw [show j + (l - j) - 1 = l - 1 by omega] at e2
  rw [show i + (l - i) - 1 = l - 1 by omega] at e3
  have := b.fl_alt S hA (j - 1)
  rw [show j - 1 + 1 = j by omega, e2, ← e3, e1] at this
  exact this rfl

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
  (hmin : ∀ c : CWord D.Q, c.Alt S → b.n ≤ c.n)

theorem vt_walk (t : ℕ) : (b.fl t).tgt = b.vt (t + 1) := b.fl_walk t

theorem vt_per (t : ℕ) : b.vt (t + b.n) = b.vt t := by simp only [vt, fl_per]

include hA hmin in
/-- **Lemma 4.2**: the two loops at a repeated vertex meet only there. -/
theorem no_common {i j s t : ℕ} (hij : i < j) (hjn : j < i + b.n) (hv : b.vt i = b.vt j)
    (hs1 : i < s) (hs2 : s < j) (ht1 : j < t) (ht2 : t < i + b.n) (hst : b.vt s = b.vt t) :
    False := by
  let g : ℕ → Letter D.Q := fun r ↦
    if r < s - i then (b.fl (s - 1 - r)).inv else b.fl (j + (r - (s - i)))
  have hju := b.junction S hA hmin i (j - i) (by omega) (by omega)
    (by rw [show i + (j - i) = j by omega]; exact hv)
  rw [show i + (j - i) - 1 = j - 1 by omega] at hju
  have hjs := b.junction S hA hmin s (t - s) (by omega) (by omega)
    (by rw [show s + (t - s) = t by omega]; exact hst)
  rw [show s + (t - s) - 1 = t - 1 by omega] at hjs
  refine b.shorter_false S hmin g ((s - i) + (t - j)) (by omega) (by omega) (fun r hr ↦ ?_) ?_
    (fun r hr ↦ ?_) ?_
  · -- walk
    simp only [g]
    by_cases h1 : r + 1 < s - i
    · rw [if_pos (show r < s - i by omega), if_pos h1, Letter.tgt_inv, Letter.src_inv, b.vt_walk,
        show s - 1 - (r + 1) + 1 = s - 1 - r by omega]; rfl
    by_cases h2 : r < s - i
    · rw [if_pos h2, if_neg h1, Letter.tgt_inv, show r + 1 - (s - i) = 0 by omega, Nat.add_zero,
        show s - 1 - r = i by omega]
      exact hv
    · rw [if_neg h2, if_neg h1, b.fl_walk]
      congr 2; omega
  · -- closed
    simp only [g]
    rw [if_neg (by omega), if_pos (by omega), Letter.src_inv, b.vt_walk, b.vt_walk,
      show j + ((s - i) + (t - j) - 1 - (s - i)) + 1 = t by omega,
      show s - 1 - 0 + 1 = s by omega]
    exact hst.symm
  · -- internal alternation
    simp only [g]
    by_cases h1 : r + 1 < s - i
    · rw [if_pos h1, if_pos (show r < s - i by omega), Signs.st_inv, Signs.en_inv]
      have := b.fl_alt S hA (s - 1 - (r + 1))
      rw [show s - 1 - (r + 1) + 1 = s - 1 - r by omega] at this
      exact Ne.symm this
    by_cases h2 : r < s - i
    · rw [if_pos h2, if_neg h1, Signs.en_inv, show r + 1 - (s - i) = 0 by omega, Nat.add_zero,
        show s - 1 - r = i by omega, hju]
      have := b.fl_alt S hA (j - 1)
      rwa [show j - 1 + 1 = j by omega] at this
    · rw [if_neg h2, if_neg h1]
      have := b.fl_alt S hA (j + (r - (s - i)))
      rwa [show j + (r - (s - i)) + 1 = j + (r + 1 - (s - i)) by omega] at this
  · -- cyclic junction
    simp only [g]
    rw [if_pos (by omega), if_neg (by omega), Signs.st_inv,
      show j + ((s - i) + (t - j) - 1 - (s - i)) = t - 1 by omega, show s - 1 - 0 = s - 1 by omega,
      ← hjs]
    have := b.fl_alt S hA (s - 1)
    rw [show s - 1 + 1 = s by omega] at this
    exact Ne.symm this

include hA hmin in
/-- The ends of a simple loop whose junction fails have the same direction. -/
theorem same_dir {i g : ℕ} (hg : 0 < g) (hgn : g < b.n) (hv : b.vt i = b.vt (i + g))
    (hsimp : ∀ s s', s < g → s' < g → b.vt (i + s) = b.vt (i + s') → s = s') :
    (b.fl (i + g - 1)).2 = (b.fl i).2 := by
  have hj := b.junction S hA hmin i g hg hgn hv
  by_contra hne
  have hend : (b.fl (i + g - 1)).tgt = b.vt i := by
    rw [b.vt_walk, show i + g - 1 + 1 = i + g by omega]; exact hv.symm
  have hal := b.fl_alt S hA i
  rcases hf : b.fl i with ⟨a, d⟩
  rcases hf' : b.fl (i + g - 1) with ⟨a', d'⟩
  rw [hf, hf'] at hne
  rw [hf, hf'] at hj
  rw [hf'] at hend
  have hsrc : (b.fl i).src = b.vt i := rfl
  rw [hf] at hsrc
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [show i + 1 - 1 = i by omega, hf] at hf'
    simp only [Prod.mk.injEq] at hf'
    exact hne hf'.2.symm
  cases d <;> cases d' <;> simp at hne
  · -- `a⁻¹ … a'`
    simp only [Signs.st_false, Signs.en_true] at hj
    simp only [Letter.src, Bool.false_eq_true, if_false] at hsrc
    simp only [Letter.tgt, if_true] at hend
    have haa : a = a' := by
      by_contra hn; exact S.hε a a' hn (hsrc.trans hend.symm) hj
    subst haa
    have h1 : b.vt (i + g - 1) = b.vt (i + 1) := by
      show (b.fl (i + g - 1)).src = _
      rw [hf', ← b.vt_walk, hf]; rfl
    have := hsimp (g - 1) 1 (by omega) (by omega) (by rw [show i + (g - 1) = i + g - 1 by omega]; exact h1)
    have hg2 : g = 2 := by omega
    subst hg2
    rw [show i + 2 - 1 = i + 1 by omega] at hf'
    rw [hf', hf] at hal
    exact hal rfl
  · -- `a … a'⁻¹`
    simp only [Signs.st_true, Signs.en_false] at hj
    simp only [Letter.src, if_true] at hsrc
    simp only [Letter.tgt, Bool.false_eq_true, if_false] at hend
    have haa : a = a' := by
      by_contra hn; exact S.hσ a a' hn (hsrc.trans hend.symm) hj
    subst haa
    have h1 : b.vt (i + g - 1) = b.vt (i + 1) := by
      show (b.fl (i + g - 1)).src = _
      rw [hf', ← b.vt_walk, hf]; rfl
    have := hsimp (g - 1) 1 (by omega) (by omega) (by rw [show i + (g - 1) = i + g - 1 by omega]; exact h1)
    have hg2 : g = 2 := by omega
    subst hg2
    rw [show i + 2 - 1 = i + 1 by omega] at hf'
    rw [hf', hf] at hal
    exact hal rfl

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)

/-- The letter function of the shape `P ω Q ω⁻¹` built from `b`. -/
def shapeFn (i gm m q : ℕ) (Qf : ℕ → Letter D.Q) (r : ℕ) : Letter D.Q :=
  if r < gm + m then b.fl (i + r)
  else if r < gm + m + q then Qf (r - (gm + m))
  else (b.fl (i + gm + m - 1 - (r - (gm + m + q)))).inv

section Builder

variable {i gm m q : ℕ} (hgm : 0 < gm) (hq : 0 < q) {Qf : ℕ → Letter D.Q}
  (hQw : ∀ s, s + 1 < q → (Qf s).tgt = (Qf (s + 1)).src)
  (hQ0 : (Qf 0).src = b.vt (i + gm + m)) (hQq : (Qf (q - 1)).tgt = b.vt (i + gm + m))
  (hvj : b.vt (i + gm) = b.vt i)
include hgm hq hQw hQ0 hQq hvj

theorem shape_walk : ∀ r, r + 1 < gm + m + q + m →
    (b.shapeFn i gm m q Qf r).tgt = (b.shapeFn i gm m q Qf (r + 1)).src := by
  intro r hr
  simp only [shapeFn]
  by_cases h1 : r + 1 < gm + m
  · rw [if_pos (by omega), if_pos h1, b.fl_walk, Nat.add_assoc]
  by_cases h2 : r < gm + m
  · rw [if_pos h2, if_neg h1, if_pos (by omega), show r + 1 - (gm + m) = 0 by omega, hQ0,
      b.vt_walk, show i + r + 1 = i + gm + m by omega]
  by_cases h3 : r + 1 < gm + m + q
  · rw [if_neg h2, if_pos (by omega), if_neg h1, if_pos h3, hQw _ (by omega)]
    congr 2; omega
  by_cases h4 : r < gm + m + q
  · rw [if_neg h2, if_pos h4, if_neg h1, if_neg h3, Letter.src_inv,
      show r - (gm + m) = q - 1 by omega, hQq, show r + 1 - (gm + m + q) = 0 by omega,
      Nat.sub_zero, b.vt_walk, show i + gm + m - 1 + 1 = i + gm + m by omega]
  · rw [if_neg h2, if_neg h4, if_neg h1, if_neg h3, Letter.tgt_inv, Letter.src_inv, b.vt_walk]
    show b.vt _ = b.vt _
    congr 1; omega

theorem shape_closed :
    (b.shapeFn i gm m q Qf (gm + m + q + m - 1)).tgt = (b.shapeFn i gm m q Qf 0).src := by
  simp only [shapeFn]
  rw [if_pos (show 0 < gm + m by omega), Nat.add_zero]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [if_neg (by omega), if_pos (by omega), show gm + 0 + q + 0 - 1 - (gm + 0) = q - 1 by omega,
      hQq, Nat.add_zero, hvj]; rfl
  · rw [if_neg (by omega), if_neg (by omega), Letter.tgt_inv,
      show i + gm + m - 1 - (gm + m + q + m - 1 - (gm + m + q)) = i + gm by omega]
    exact hvj

variable (hQa : ∀ s, s + 1 < q → S.st (Qf (s + 1)) ≠ S.en (Qf s))
  (hc : S.st (Qf 0) ≠ S.en (b.fl (i + gm + m - 1)))
  (hd : 0 < m → S.en (b.fl (i + gm + m - 1)) ≠ S.en (Qf (q - 1)))
  (he : m = 0 → S.st (b.fl i) ≠ S.en (Qf (q - 1)))
  (hJ1 : 0 < m → S.st (b.fl i) ≠ S.st (b.fl (i + gm)))

/-- The cyclic word of the shape. -/
def shapeC : CWord D.Q :=
  mkC (b.shapeFn i gm m q Qf) (gm + m + q + m) (by omega)
    (b.shape_walk hgm hq hQw hQ0 hQq hvj) (b.shape_closed hgm hq hQw hQ0 hQq hvj)

include hA hQa hc hd he hJ1 in
theorem shapeC_alt : (b.shapeC hgm hq hQw hQ0 hQq hvj).Alt S := by
  refine mkC_alt _ _ _ _ _ S (fun r hr ↦ ?_) ?_
  · simp only [shapeFn]
    by_cases h1 : r + 1 < gm + m
    · rw [if_pos h1, if_pos (by omega)]
      have := b.fl_alt S hA (i + r); rwa [Nat.add_assoc] at this
    by_cases h2 : r < gm + m
    · rw [if_neg h1, if_pos (by omega), if_pos h2, show r + 1 - (gm + m) = 0 by omega,
        show i + r = i + gm + m - 1 by omega]
      exact hc
    by_cases h3 : r + 1 < gm + m + q
    · rw [if_neg h1, if_pos h3, if_neg h2, if_pos (by omega),
        show r + 1 - (gm + m) = r - (gm + m) + 1 by omega]
      exact hQa _ (by omega)
    by_cases h4 : r < gm + m + q
    · rw [if_neg h1, if_neg h3, if_neg h2, if_pos h4, Signs.st_inv,
        show r + 1 - (gm + m + q) = 0 by omega, Nat.sub_zero, show r - (gm + m) = q - 1 by omega]
      exact hd (by omega)
    · rw [if_neg h1, if_neg h3, if_neg h2, if_neg h4, Signs.st_inv, Signs.en_inv]
      have := b.fl_alt S hA (i + gm + m - 1 - (r + 1 - (gm + m + q)))
      rw [show i + gm + m - 1 - (r + 1 - (gm + m + q)) + 1 =
        i + gm + m - 1 - (r - (gm + m + q)) by omega] at this
      exact Ne.symm this
  · simp only [shapeFn]
    rw [if_pos (show 0 < gm + m by omega), Nat.add_zero]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [if_neg (by omega), if_pos (by omega),
        show gm + 0 + q + 0 - 1 - (gm + 0) = q - 1 by omega]
      exact he rfl
    · rw [if_neg (by omega), if_neg (by omega), Signs.en_inv,
        show i + gm + m - 1 - (gm + m + q + m - 1 - (gm + m + q)) = i + gm by omega]
      exact hJ1 hm

theorem shapeC_letters :
    (b.shapeC hgm hq hQw hQ0 hQq hvj).letters =
      (List.ofFn fun s : Fin gm ↦ b.fl (i + s)) ++ (List.ofFn fun t : Fin m ↦ b.fl (i + gm + t)) ++
        (List.ofFn fun s : Fin q ↦ Qf s) ++ invLetters (List.ofFn fun t : Fin m ↦ b.fl (i + gm + t)) := by
  apply List.ext_getElem
  · simp [shapeC, mkC, invLetters]; omega
  intro r h1 h2
  simp only [shapeC, mkC, List.getElem_ofFn, shapeFn]
  simp only [List.length_ofFn, List.length_append, invLetters, List.length_reverse, List.length_map]
    at h2
  by_cases ha : r < gm
  · rw [if_pos (by omega)]
    simp [List.getElem_append, ha, show r < gm + m by omega, show r < gm + m + q by omega]
  by_cases hb : r < gm + m
  · rw [if_pos hb]
    simp only [List.getElem_append, List.length_append, List.length_ofFn,
      show r < gm + m by omega, show r < gm + m + q by omega, ha, dite_true, dite_false,
      List.getElem_ofFn]
    congr 1; omega
  by_cases hc' : r < gm + m + q
  · rw [if_neg hb, if_pos hc']
    simp only [List.getElem_append, List.length_append, List.length_ofFn, hb, hc', dite_true,
      dite_false, List.getElem_ofFn]
  · rw [if_neg hb, if_neg hc']
    simp only [List.getElem_append, List.length_append, List.length_ofFn, hc', dite_false]
    simp [invLetters, List.getElem_reverse]
    congr 2; omega

end Builder

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
  (hmin : ∀ c : CWord D.Q, c.Alt S → b.n ≤ c.n)

/-- The selection data of a minimal cyclic word with a repeated vertex. -/
structure SelData where
  i : ℕ
  gm : ℕ
  i2 : ℕ
  i3 : ℕ
  hgm : 0 < gm
  hgn : gm < b.n
  hj2 : i + gm ≤ i2
  h23 : i2 < i3
  h3 : i3 ≤ i + b.n
  hq : i3 - i2 < b.n
  hvi : b.vt i = b.vt (i + gm)
  hv23 : b.vt i2 = b.vt i3
  FP : ∀ s s', s < gm → s' < gm → b.vt (i + s) = b.vt (i + s') → s = s'
  FQ : ∀ s s', s < i3 - i2 → s' < i3 - i2 → b.vt (i2 + s) = b.vt (i2 + s') → s = s'
  Fω : ∀ t t', t ≤ i2 - (i + gm) → t' ≤ i2 - (i + gm) →
    b.vt (i + gm + t) = b.vt (i + gm + t') → t = t'
  FPω : ∀ s t, s < gm → t ≤ i2 - (i + gm) → b.vt (i + s) = b.vt (i + gm + t) → s = 0 ∧ t = 0
  FQω : ∀ s t, s < i3 - i2 → t ≤ i2 - (i + gm) → b.vt (i2 + s) = b.vt (i + gm + t) →
    s = 0 ∧ t = i2 - (i + gm)
  FPQ : ∀ s s', s < gm → s' < i3 - i2 → b.vt (i + s) = b.vt (i2 + s') →
    i2 = i + gm ∧ s = 0 ∧ s' = 0

include hA hmin in
theorem exists_selData (hrep : ∃ p q : ℕ, p < q ∧ q < b.n ∧ b.vt p = b.vt q) :
    Nonempty (SelData b) := by
  classical
  have hex : ∃ g, 0 < g ∧ g < b.n ∧ ∃ i, b.vt i = b.vt (i + g) := by
    obtain ⟨p, q, hpq, hq, hv⟩ := hrep
    exact ⟨q - p, by omega, by omega, p, by rw [show p + (q - p) = q by omega]; exact hv⟩
  set gm := Nat.find hex
  obtain ⟨hgm, hgn, i, hi⟩ := Nat.find_spec hex
  have hgmin : ∀ g, 0 < g → g < gm → ∀ i', b.vt i' ≠ b.vt (i' + g) := fun g h0 hg i' h ↦
    Nat.find_min hex hg ⟨h0, by omega, i', h⟩
  set j := i + gm
  have FP : ∀ s s', s < gm → s' < gm → b.vt (i + s) = b.vt (i + s') → s = s' := by
    intro s s' hs hs' h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hgmin (s' - s) (by omega) (by omega) (i + s)
        (by rw [show i + s + (s' - s) = i + s' by omega]; exact h)
    · exact hgmin (s - s') (by omega) (by omega) (i + s')
        (by rw [show i + s' + (s - s') = i + s by omega]; exact h.symm)
  have hun : ∀ t, j < t → t < i + b.n → b.vt t ≠ b.vt i := fun t h1 h2 h ↦
    b.two_visits S hA hmin (show i < j by omega) h1 h2 hi (by rw [← hi]; exact h.symm)
  have hcom := fun s t (hs1 : i < s) (hs2 : s < j) (ht1 : j < t) (ht2 : t < i + b.n) h ↦
    b.no_common S hA hmin (show i < j by omega) (by omega) hi hs1 hs2 ht1 ht2 h
  let Rep : ℕ → ℕ → Prop := fun s1 s2 ↦ j ≤ s1 ∧ s1 < s2 ∧ s2 < i + b.n ∧ b.vt s1 = b.vt s2
  by_cases hr : ∃ s2 s1, Rep s1 s2
  · set i3 := Nat.find hr
    obtain ⟨i2, hj2, h23, h3, hv23⟩ := Nat.find_spec hr
    have hmin3 : ∀ s1 s2, j ≤ s1 → s1 < s2 → s2 < i3 → b.vt s1 ≠ b.vt s2 := fun s1 s2 h1 h2 h3' h ↦
      Nat.find_min hr h3' ⟨s1, h1, h2, by omega, h⟩
    refine ⟨⟨i, gm, i2, i3, hgm, hgn, hj2, h23, h3.le, by omega, hi, hv23, FP, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro s s' hs hs' h
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hmin3 (i2 + s) (i2 + s') (by omega) (by omega) (by omega) h
      · exact hmin3 (i2 + s') (i2 + s) (by omega) (by omega) (by omega) h.symm
    · intro t t' ht ht' h
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hmin3 (i + gm + t) (i + gm + t') (by omega) (by omega) (by omega) h
      · exact hmin3 (i + gm + t') (i + gm + t) (by omega) (by omega) (by omega) h.symm
    · intro s t hs ht h
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · subst hs0
        refine ⟨rfl, ?_⟩
        by_contra ht0
        exact hun (i + gm + t) (by omega) (by omega) (by rw [Nat.add_zero] at h; exact h.symm)
      · exfalso
        rcases Nat.eq_zero_or_pos t with ht0 | ht0
        · subst ht0
          have := FP s 0 hs hgm (by rw [Nat.add_zero, hi]; rw [Nat.add_zero] at h; exact h)
          omega
        · exact hcom (i + s) (i + gm + t) (by omega) (by omega) (by omega) (by omega) h
    · intro s t hs ht h
      by_contra hne
      rcases Nat.lt_or_ge (i + gm + t) (i2 + s) with hlt | hge
      · exact hmin3 (i + gm + t) (i2 + s) (by omega) hlt (by omega) h.symm
      · omega
    · intro s s' hs hs' h
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · subst hs0
        by_contra hne
        have : j < i2 + s' := by omega
        exact hun (i2 + s') this (by omega) (by rw [Nat.add_zero] at h; exact h.symm)
      · exfalso
        rcases Nat.lt_or_ge j (i2 + s') with hlt | hge
        · exact hcom (i + s) (i2 + s') (by omega) (by omega) hlt (by omega) h
        · have e : i2 + s' = j := by omega
          rw [e] at h
          have := FP s 0 hs hgm (by rw [Nat.add_zero, hi]; exact h)
          omega
  · push Not at hr
    have hnr : ∀ s1 s2, j ≤ s1 → s1 < s2 → s2 < i + b.n → b.vt s1 ≠ b.vt s2 := fun s1 s2 h1 h2 h3 h ↦
      hr s2 s1 ⟨h1, h2, h3, h⟩
    refine ⟨⟨i, gm, j, i + b.n, hgm, hgn, le_rfl, by omega, le_rfl, by omega, hi,
      by rw [b.vt_per, ← hi], FP, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro s s' hs hs' h
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hnr (j + s) (j + s') (by omega) (by omega) (by omega) h
      · exact hnr (j + s') (j + s) (by omega) (by omega) (by omega) h.symm
    · intro t t' ht ht' _; omega
    · intro s t hs ht h
      have ht0 : t = 0 := by omega
      subst ht0
      refine ⟨FP s 0 hs hgm (by rw [Nat.add_zero, hi]; rw [Nat.add_zero] at h; exact h), rfl⟩
    · intro s t hs ht h
      have ht0 : t = 0 := by omega
      subst ht0
      refine ⟨?_, by omega⟩
      by_contra hs0
      exact hnr j (j + s) le_rfl (by omega) (by omega) (by rw [Nat.add_zero] at h; exact h.symm)
    · intro s s' hs hs' h
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · subst hs0
        refine ⟨rfl, rfl, ?_⟩
        by_contra hne
        exact hun (j + s') (by omega) (by omega) (by rw [Nat.add_zero] at h; exact h.symm)
      · exfalso
        rcases Nat.eq_zero_or_pos s' with hs'0 | hs'0
        · subst hs'0
          have := FP s 0 hs hgm (by rw [Nat.add_zero, hi]; rw [Nat.add_zero] at h; exact h)
          omega
        · exact hcom (i + s) (j + s') (by omega) (by omega) (by omega) (by omega) h

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
  (hmin : ∀ c : CWord D.Q, c.Alt S → b.n ≤ c.n)

theorem fl_src (t : ℕ) : (b.fl t).src = b.vt t := rfl

include hA hmin in
/-- **Assembly of shape 2** from selection data and a choice of the loop `Q`. -/
theorem not_isBrickFinite_of_sel [IsAlgClosed k] [FiniteDimensional k B]
    (hKa : ∀ c : CWord D.Q, c.Alt S → c.KillsZero) (d : SelData b) (Qf : ℕ → Letter D.Q)
    (hQw : ∀ s, s + 1 < d.i3 - d.i2 → (Qf s).tgt = (Qf (s + 1)).src)
    (hQ0 : (Qf 0).src = b.vt d.i2) (hQq : (Qf (d.i3 - d.i2 - 1)).tgt = b.vt d.i2)
    (hQa : ∀ s, s + 1 < d.i3 - d.i2 → S.st (Qf (s + 1)) ≠ S.en (Qf s))
    (hst : S.st (Qf 0) = S.st (b.fl d.i2)) (hen : S.en (Qf (d.i3 - d.i2 - 1)) = S.st (b.fl d.i2))
    (hdir : (Qf (d.i3 - d.i2 - 1)).2 = (Qf 0).2) (hdir0 : (Qf 0).2 = (b.fl d.i).2)
    (σ : ℕ → ℕ) (hσ : ∀ s < d.i3 - d.i2, σ s < d.i3 - d.i2)
    (hσi : ∀ s s', s < d.i3 - d.i2 → s' < d.i3 - d.i2 → σ s = σ s' → s = s')
    (hσ0 : ∀ s < d.i3 - d.i2, σ s = 0 → s = 0)
    (hQv : ∀ s < d.i3 - d.i2, (Qf s).src = b.vt (d.i2 + σ s)) : ¬ IsBrickFinite B := by
  obtain ⟨i, gm, i2, i3, hgm, hgn, hj2, h23, h3, hq, hvi, hv23, FP, FQ, Fω, FPω, FQω, FPQ⟩ := d
  dsimp only at *
  set m := i2 - (i + gm) with hm
  set q := i3 - i2 with hqd
  have e2 : i + gm + m = i2 := by omega
  have hq0 : 0 < q := by omega
  have hQ0' : (Qf 0).src = b.vt (i + gm + m) := by rw [e2]; exact hQ0
  have hQq' : (Qf (q - 1)).tgt = b.vt (i + gm + m) := by rw [e2]; exact hQq
  have hj1 : S.st (b.fl i) ≠ S.st (b.fl (i + gm)) := by
    have e := b.junction S hA hmin i gm hgm hgn hvi
    have a := b.fl_alt S hA (i + gm - 1)
    rw [show i + gm - 1 + 1 = i + gm by omega] at a
    rw [e]; exact Ne.symm a
  have halt2 : S.st (b.fl i2) ≠ S.en (b.fl (i + gm + m - 1)) := by
    have a := b.fl_alt S hA (i2 - 1)
    rw [show i2 - 1 + 1 = i2 by omega] at a
    rw [show i + gm + m - 1 = i2 - 1 by omega]; exact a
  have hcA := b.shapeC_alt S hA hgm hq0 hQw hQ0' hQq' hvi.symm hQa
    (by rw [hst]; exact halt2) (fun _ ↦ by rw [hen]; exact Ne.symm halt2)
    (fun h0 ↦ by rw [hen, show i2 = i + gm by omega]; exact hj1) (fun _ ↦ hj1)
  have hcl := b.shapeC_letters hgm hq0 hQw hQ0' hQq' hvi.symm
  set c := b.shapeC hgm hq0 hQw hQ0' hQq' hvi.symm
  set Pl := List.ofFn fun s : Fin gm ↦ b.fl (i + s) with hPl
  set ωl := List.ofFn fun t : Fin m ↦ b.fl (i + gm + t) with hωl
  set Ql := List.ofFn fun s : Fin q ↦ Qf s with hQl
  have hP : Pl ≠ [] := by rw [hPl, Ne, List.ofFn_eq_nil_iff]; omega
  have hQ : Ql ≠ [] := by rw [hQl, Ne, List.ofFn_eq_nil_iff]; omega
  have lP : Pl.length = gm := List.length_ofFn
  have lω : ωl.length = m := List.length_ofFn
  have lQ : Ql.length = q := List.length_ofFn
  have gP : ∀ s (hs : s < Pl.length), Pl[s] = b.fl (i + s) := fun s hs ↦ by
    simp [hPl]
  have gω : ∀ t (ht : t < ωl.length), ωl[t] = b.fl (i + gm + t) := fun t ht ↦ by
    simp [hωl]
  have gQ : ∀ s (hs : s < Ql.length), Ql[s] = Qf s := fun s hs ↦ by
    simp [hQl]
  have hPh : Pl.head hP = b.fl i := by rw [List.head_eq_getElem, gP]; simp
  have hPl' : Pl.getLast hP = b.fl (i + gm - 1) := by
    rw [List.getLast_eq_getElem, gP, lP]; congr 1; omega
  have hQh : Ql.head hQ = Qf 0 := by rw [List.head_eq_getElem, gQ]
  have hQl' : Ql.getLast hQ = Qf (q - 1) := by rw [List.getLast_eq_getElem, gQ, lQ]
  have hωv : ∀ t ≤ m, ωv ωl Ql hQ t = b.vt (i + gm + t) := by
    intro t ht
    unfold ωv
    split_ifs with h
    · rw [gω]; rfl
    · rw [lω] at h
      rw [hQh, hQ0', show t = m by omega]
  have hH := c.shape_coincide hcl hP hQ
    (fun s s' hs hs' h ↦ by
      rw [gP, gP, fl_src, fl_src] at h; rw [lP] at hs hs'; exact FP s s' hs hs' h)
    (fun s s' hs hs' h ↦ by
      rw [gQ, gQ] at h; rw [lQ] at hs hs'
      rw [hQv s hs, hQv s' hs'] at h
      exact hσi s s' hs hs' (FQ _ _ (hσ s hs) (hσ s' hs') h))
    (fun t t' ht ht' h ↦ by
      rw [lω] at ht ht'; rw [hωv t ht, hωv t' ht'] at h; exact Fω t t' ht ht' h)
    (fun s t hs ht h ↦ by
      rw [lω] at ht; rw [lP] at hs; rw [gP, fl_src, hωv t ht] at h; exact FPω s t hs ht h)
    (fun s t hs ht h ↦ by
      rw [lω] at ht ⊢; rw [lQ] at hs; rw [gQ, hQv s hs, hωv t ht] at h
      obtain ⟨h1, h2⟩ := FQω (σ s) t (hσ s hs) ht h
      exact ⟨hσ0 s hs h1, h2⟩)
    (fun s s' hs hs' h ↦ by
      rw [lω]; rw [lP] at hs; rw [lQ] at hs'; rw [gP, gQ, fl_src, hQv s' hs'] at h
      obtain ⟨h1, h2, h3⟩ := FPQ s (σ s') hs (hσ s' hs') h
      exact ⟨by omega, h2, hσ0 s' hs' h3⟩)
  have hK := hKa c hcA
  have hPj : S.st (Pl.head hP) = S.en (Pl.getLast hP) := by
    rw [hPh, hPl']; exact b.junction S hA hmin i gm hgm hgn hvi
  have hPt : (Pl.getLast hP).2 = (Pl.head hP).2 := by
    rw [hPh, hPl']; exact b.same_dir S hA hmin hgm hgn hvi FP
  have hQt : (Ql.getLast hQ).2 = (Ql.head hQ).2 := by rw [hQh, hQl']; exact hdir
  have hPQ : (Pl.head hP).2 = (Ql.head hQ).2 := by rw [hPh, hQh]; exact hdir0.symm
  have hN := c.shape2_hN S hcA hK hcl hP hQ hPj hPt hQt hPQ hH 1
  exact c.not_isBrickFinite S hcA hK (c.prim_of_plusSets S hcA 1 hN) 1
    (c.isBrick_of_plusSets' S hcA hK 1 hN)

end CWord

namespace CWord

variable {D : MonomialData k B} (S : D.Signs)

/-- Over good signs of a quadratic algebra, alternating cyclic words kill zero paths. -/
theorem killsZero_of_alt (hS : S.Good) (hQ : D.IsQuadratic) (c : CWord D.Q) (hc : c.Alt S) :
    c.KillsZero :=
  c.killsZero_of_allowed S hc hQ fun q ↦
    (Signs.allowedPair_iff (l := c.lt q) (l' := c.lt (c.succ q)) hS (c.lt_tgt q)).mpr (hc q)

variable (b : CWord D.Q) (hA : b.Alt S) (hmin : ∀ c : CWord D.Q, c.Alt S → b.n ≤ c.n)

include hA hmin in
/-- Shape 2 with `Q` in its own direction. -/
theorem not_isBrickFinite_sel_pos [IsAlgClosed k] [FiniteDimensional k B]
    (hKa : ∀ c : CWord D.Q, c.Alt S → c.KillsZero) (d : SelData b)
    (hdir : (b.fl d.i2).2 = (b.fl d.i).2) : ¬ IsBrickFinite B := by
  have hq := d.hq
  have h23 := d.h23
  have hjun := b.junction S hA hmin d.i2 (d.i3 - d.i2) (by omega) hq
    (by rw [show d.i2 + (d.i3 - d.i2) = d.i3 by omega]; exact d.hv23)
  refine b.not_isBrickFinite_of_sel S hA hmin hKa d (fun s ↦ b.fl (d.i2 + s))
    (fun s _ ↦ by rw [b.fl_walk, Nat.add_assoc]) (by rw [Nat.add_zero]; rfl)
    (by rw [b.vt_walk, show d.i2 + (d.i3 - d.i2 - 1) + 1 = d.i3 by omega]; exact d.hv23.symm)
    (fun s _ ↦ by have := b.fl_alt S hA (d.i2 + s); rwa [Nat.add_assoc] at this)
    (by rw [Nat.add_zero])
    (by rw [hjun, show d.i2 + (d.i3 - d.i2) - 1 = d.i2 + (d.i3 - d.i2 - 1) by omega])
    ?_ (by rw [Nat.add_zero]; exact hdir) id (fun s hs ↦ hs) (fun s s' _ _ h ↦ h)
    (fun s _ h ↦ h) (fun s _ ↦ rfl)
  have := b.same_dir S hA hmin (i := d.i2) (g := d.i3 - d.i2) (by omega) hq
    (by rw [show d.i2 + (d.i3 - d.i2) = d.i3 by omega]; exact d.hv23) d.FQ
  rw [Nat.add_zero, show d.i2 + (d.i3 - d.i2 - 1) = d.i2 + (d.i3 - d.i2) - 1 by omega]
  exact this

include hA hmin in
/-- Shape 2 with `Q` reversed. -/
theorem not_isBrickFinite_sel_neg [IsAlgClosed k] [FiniteDimensional k B]
    (hKa : ∀ c : CWord D.Q, c.Alt S → c.KillsZero) (d : SelData b)
    (hdir : ¬ (b.fl d.i2).2 = (b.fl d.i).2) : ¬ IsBrickFinite B := by
  have hq := d.hq
  have h23 := d.h23
  have hjun := b.junction S hA hmin d.i2 (d.i3 - d.i2) (by omega) hq
    (by rw [show d.i2 + (d.i3 - d.i2) = d.i3 by omega]; exact d.hv23)
  have hsd := b.same_dir S hA hmin (i := d.i2) (g := d.i3 - d.i2) (by omega) hq
    (by rw [show d.i2 + (d.i3 - d.i2) = d.i3 by omega]; exact d.hv23) d.FQ
  rw [show d.i2 + (d.i3 - d.i2) - 1 = d.i3 - 1 by omega] at hjun hsd
  refine b.not_isBrickFinite_of_sel S hA hmin hKa d (fun s ↦ (b.fl (d.i3 - 1 - s)).inv)
    (fun s _ ↦ ?_) ?_ ?_ (fun s _ ↦ ?_) ?_ ?_ ?_ ?_
    (fun s ↦ if s = 0 then 0 else d.i3 - d.i2 - s) (fun s hs ↦ by split_ifs <;> omega)
    (fun s s' _ _ h ↦ by split_ifs at h <;> omega)
    (fun s _ h ↦ by split_ifs at h <;> omega) (fun s hs ↦ ?_)
  · rw [Letter.tgt_inv, Letter.src_inv, b.vt_walk]
    show b.vt _ = b.vt _
    congr 1; omega
  · rw [Letter.src_inv, b.vt_walk, show d.i3 - 1 - 0 + 1 = d.i3 by omega]; exact d.hv23.symm
  · rw [Letter.tgt_inv, show d.i3 - 1 - (d.i3 - d.i2 - 1) = d.i2 by omega]; rfl
  · rw [Signs.st_inv, Signs.en_inv]
    have := b.fl_alt S hA (d.i3 - 1 - (s + 1))
    rw [show d.i3 - 1 - (s + 1) + 1 = d.i3 - 1 - s by omega] at this
    exact Ne.symm this
  · rw [Signs.st_inv, Nat.sub_zero, hjun]
  · rw [Signs.en_inv, show d.i3 - 1 - (d.i3 - d.i2 - 1) = d.i2 by omega]
  · show (!(b.fl _).2) = (!(b.fl _).2)
    rw [show d.i3 - 1 - (d.i3 - d.i2 - 1) = d.i2 by omega, Nat.sub_zero, hsd]
  · show (!(b.fl _).2) = _
    rw [Nat.sub_zero, hsd]
    revert hdir
    cases (b.fl d.i2).2 <;> cases (b.fl d.i).2 <;> simp
  · rw [Letter.src_inv, b.vt_walk]
    split_ifs with h0
    · subst h0
      rw [show d.i3 - 1 - 0 + 1 = d.i3 by omega, Nat.add_zero]; exact d.hv23.symm
    · congr 1; omega

end CWord

namespace MonomialData

/-- **Plamondon**: over a gentle algebra, an allowed closed word gives infinitely many bricks. -/
theorem not_isBrickFinite_of_hasClosed [IsAlgClosed k] [FiniteDimensional k B]
    (D : MonomialData k B) (hD : D.IsGentle) (h : D.HasClosed) : ¬ IsBrickFinite B := by
  classical
  obtain ⟨S, hS⟩ := exists_good_signs hD
  obtain ⟨x, ω, hne, hw, he, hch, hcy⟩ := h
  obtain ⟨b0, hA0, -⟩ := D.exists_band_of_closed hD S x ω hne hw he hch hcy
  have hex : ∃ N, ∃ c : CWord D.Q, c.Alt S ∧ c.n = N := ⟨_, b0, hA0, rfl⟩
  obtain ⟨b, hA, hbN⟩ := Nat.find_spec hex
  have hmin : ∀ c : CWord D.Q, c.Alt S → b.n ≤ c.n := fun c hc ↦
    hbN ▸ Nat.find_min' hex ⟨c, hc, rfl⟩
  have hKa : ∀ c : CWord D.Q, c.Alt S → c.KillsZero := fun c hc ↦
    CWord.killsZero_of_alt S hS hD.2.1 c hc
  by_cases hrep : ∃ p q : ℕ, p < q ∧ q < b.n ∧ b.vt p = b.vt q
  · obtain ⟨d⟩ := b.exists_selData S hA hmin hrep
    by_cases hdir : (b.fl d.i2).2 = (b.fl d.i).2
    · exact b.not_isBrickFinite_sel_pos S hA hmin hKa d hdir
    · exact b.not_isBrickFinite_sel_neg S hA hmin hKa d hdir
  · push Not at hrep
    have hK := hKa b hA
    have hvv : ∀ p : Fin b.n, b.vtx p = b.vt p.val := fun p ↦ by
      show (b.lt p).src = (b.fl p.val).src
      rw [b.fl_val]
      congr 2
      exact Fin.ext (Nat.mod_eq_of_lt p.isLt).symm
    have hv : Function.Injective b.vtx := by
      intro p q hpq
      rw [hvv, hvv] at hpq
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · exact hrep _ _ hlt q.isLt hpq
      · exact hrep _ _ hlt p.isLt hpq.symm
    have hprim : ∀ p q : Fin b.n, b.rightW p = b.rightW q → p = q := by
      intro p q h
      have h0 : b.lt p = b.lt q := by have := congrFun h 0; simpa [CWord.rightW] using this
      exact hv (by simp [CWord.vtx, h0])
    exact b.not_isBrickFinite S hA hK hprim 1 (b.isBrick_of_vtx_injective S hA hK hprim hv 1)

end MonomialData

end BrickAccessibility
