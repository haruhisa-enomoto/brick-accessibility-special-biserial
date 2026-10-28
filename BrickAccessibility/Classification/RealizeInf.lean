module

public import BrickAccessibility.Classification.BandShift
public import BrickAccessibility.Classification.Filtration

/-!
# Realization of pairs with an infinite half-word

Shifting a pair of half-words across the first letter of an infinite side
preserves the vanishing of its pair functor (`shift_le_iff`). A nonzero pair
functor forces both sides into the finite supports of the dimension formula, so
iterating the shift gives:

* a nonzero pair never has exactly one infinite side (`le_of_inf_fin`);
* a nonzero pair of infinite half-words is the pair at the first position of a
  primitive band (`exists_band`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} (S : D.Signs)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- The letters of a valid infinite half-word form a walk with alternating signs. -/
theorem Signs.valid_inf_facts {v : D.Q.V} {s : Bool} {f : ℕ → Letter D.Q}
    (hv : S.Valid v s (.inf f)) :
    (f 0).src = v ∧ S.st (f 0) = s ∧
      ∀ i, (f (i + 1)).src = (f i).tgt ∧ S.st (f (i + 1)) = !S.en (f i) := by
  have key : ∀ i, (f i).src = D.Q.wend v (List.ofFn fun j : Fin i ↦ f j) ∧
      S.st (f i) = S.nsign s (List.ofFn fun j : Fin i ↦ f j) := by
    intro i
    have h := hv (i + 1)
    rw [List.ofFn_succ_last] at h
    simp only [Fin.val_castSucc, Fin.val_last] at h
    exact Signs.IsHW.last S h
  refine ⟨?_, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · simpa [Statement.FinQuiver.wend] using (key 0).1
  · simpa using (key 0).2
  · rw [(key (i + 1)).1, List.ofFn_succ_last, Statement.FinQuiver.wend_append]
    simp only [Fin.val_castSucc, Fin.val_last]
    rfl
  · rw [(key (i + 1)).2, List.ofFn_succ_last, Signs.nsign_append_singleton]
    simp only [Fin.val_last]

theorem Signs.valid_tail {v : D.Q.V} {s : Bool} {f : ℕ → Letter D.Q}
    (hv : S.Valid v s (.inf f)) :
    S.Valid (f 0).tgt (!S.en (f 0)) (.inf fun i ↦ f (i + 1)) := by
  obtain ⟨-, -, hf⟩ := S.valid_inf_facts hv
  refine S.isHW_ofFn (fun i ↦ f (i + 1)) (hf 0).1 (fun i ↦ (hf (i + 1)).1) (hf 0).2 (fun i ↦ ?_)
  rw [(hf (i + 1)).2]; simp

theorem Signs.valid_cons_inv {v : D.Q.V} {s : Bool} {l : Letter D.Q} {h : HWord D.Q}
    (hl : l.src = v) (hs : S.st l = s) (hv : S.Valid v (!s) h) :
    S.Valid l.tgt (S.en l) (h.cons l.inv) := by
  refine S.valid_cons (by rw [Letter.src_inv]) (by rw [Signs.st_inv]) ?_
  rw [Letter.tgt_inv, Signs.en_inv, hl, hs]; exact hv

theorem cons_tail (f : ℕ → Letter D.Q) :
    (HWord.inf fun i ↦ f (i + 1)).cons (f 0) = .inf f := by
  simp only [HWord.cons, HWord.inf.injEq]
  funext i; cases i <;> rfl

/-- **Shifting a pair** across the first letter of an infinite side. -/
theorem Signs.shift_le_iff [FiniteDimensional k M] {v : D.Q.V} {s : Bool} {f : ℕ → Letter D.Q}
    {h' : HWord D.Q} (hv : S.Valid v s (.inf f)) (hv' : S.Valid v (!s) h') :
    S.pnum M v s (.inf f) h' ≤ S.pden M v s (.inf f) h' ↔
      S.pnum M (f 0).tgt (!S.en (f 0)) (.inf fun i ↦ f (i + 1)) (h'.cons (f 0).inv) ≤
        S.pden M (f 0).tgt (!S.en (f 0)) (.inf fun i ↦ f (i + 1)) (h'.cons (f 0).inv) := by
  obtain ⟨h0, hs0, -⟩ := S.valid_inf_facts hv
  have ht := S.valid_tail hv
  rcases hf : f 0 with ⟨a, d⟩
  rw [hf] at h0 hs0 ht
  cases d
  · -- an inverse first letter
    simp only [Letter.src, Bool.false_eq_true, if_false] at h0
    simp only [Signs.st_false] at hs0
    simp only [Letter.tgt, Bool.false_eq_true, if_false, Signs.en_false] at ht ⊢
    have hX : S.Valid (D.Q.tgt a) (!S.ε a) h' := by rw [h0, hs0]; exact hv'
    have h := (S.shift M hX ht).le_iff
    have e : (HWord.inf fun i ↦ f (i + 1)).cons (a, false) = .inf f := by
      rw [← hf]; exact cons_tail f
    rw [e, h0, hs0, S.pnum_swap, S.pden_swap] at h
    have e2 : Letter.inv ((a, false) : Letter D.Q) = (a, true) := rfl
    rw [e2, ← S.pnum_swap M _ (!S.σ a), ← S.pden_swap M _ (!S.σ a), Bool.not_not]
    exact h.symm
  · -- a direct first letter
    simp only [Letter.src, if_true] at h0
    simp only [Signs.st_true] at hs0
    simp only [Letter.tgt, if_true, Signs.en_true] at ht ⊢
    have hY : S.Valid (D.Q.src a) (!S.σ a) h' := by rw [h0, hs0]; exact hv'
    have h := (S.shift M ht hY).le_iff
    have e : (HWord.inf fun i ↦ f (i + 1)).cons (a, true) = .inf f := by
      rw [← hf]; exact cons_tail f
    rw [e, h0, hs0] at h
    exact h

/-- The other side after `n` shifts. -/
def csh (h' : HWord D.Q) (f : ℕ → Letter D.Q) : ℕ → HWord D.Q
  | 0 => h'
  | n + 1 => (csh h' f n).cons (f n).inv

/-- **Iterated shifts** of a pair along its infinite side. -/
theorem Signs.iter_shift [FiniteDimensional k M] {v : D.Q.V} {s : Bool} {f : ℕ → Letter D.Q}
    {h' : HWord D.Q} (hv : S.Valid v s (.inf f)) (hv' : S.Valid v (!s) h') (n : ℕ) :
    S.Valid (f n).src (S.st (f n)) (.inf fun i ↦ f (n + i)) ∧
      S.Valid (f n).src (!S.st (f n)) (csh h' f n) ∧
      (S.pnum M v s (.inf f) h' ≤ S.pden M v s (.inf f) h' ↔
        S.pnum M (f n).src (S.st (f n)) (.inf fun i ↦ f (n + i)) (csh h' f n) ≤
          S.pden M (f n).src (S.st (f n)) (.inf fun i ↦ f (n + i)) (csh h' f n)) := by
  obtain ⟨h0, hs0, hf⟩ := S.valid_inf_facts hv
  induction n with
  | zero =>
      simp only [Nat.zero_add, h0, hs0]
      exact ⟨hv, hv', Iff.rfl⟩
  | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hsh := S.shift_le_iff M h1 h2
      have ht := S.valid_tail h1
      have hc := S.valid_cons_inv (l := f n) (h := csh h' f n) rfl rfl h2
      have e1 : (f n).tgt = (f (n + 1)).src := (hf n).1.symm
      have e2 : (!S.en (f n)) = S.st (f (n + 1)) := (hf n).2.symm
      have e2' : S.en (f n) = !S.st (f (n + 1)) := by rw [← e2]; simp
      have e3 : (fun i ↦ f (n + (i + 1))) = fun i ↦ f (n + 1 + i) := by
        funext i; congr 1; omega
      have e4 : (csh h' f n).cons (f n).inv = csh h' f (n + 1) := rfl
      change S.Valid (f n).tgt (!S.en (f n)) (.inf fun i ↦ f (n + (i + 1))) at ht
      change _ ↔ S.pnum M (f n).tgt (!S.en (f n)) (.inf fun i ↦ f (n + (i + 1)))
        ((csh h' f n).cons (f n).inv) ≤ S.pden M (f n).tgt (!S.en (f n))
        (.inf fun i ↦ f (n + (i + 1))) ((csh h' f n).cons (f n).inv) at hsh
      rw [e1, e2, e3, e4] at hsh
      rw [e1, e2, e3] at ht
      rw [e1, e2', e4] at hc
      exact ⟨ht, hc, h3.trans hsh⟩

variable [FiniteDimensional k M]

/-- Half-words that are a side of some nonzero pair. -/
def Signs.suppSet : Set (HWord D.Q) :=
  {h | ∃ v s, S.Valid v s h ∧ S.minus M v s h < S.plus M v s h}

theorem Signs.suppSet_finite : (S.suppSet M).Finite := by
  have h1 : ∀ v s, {h | S.Valid v s h ∧ S.minus M v s h < S.plus M v s h}.Finite := by
    intro v s
    refine ((S.fam M v s).supp_finite.image Subtype.val).subset ?_
    rintro h ⟨hv, hlt⟩
    exact ⟨⟨h, hv⟩, hlt, rfl⟩
  refine (Set.finite_iUnion fun v ↦ Set.finite_iUnion fun s ↦ h1 v s).subset ?_
  rintro h ⟨v, s, hv, hlt⟩
  exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨s, hv, hlt⟩⟩

/-- Both sides of a nonzero pair lie in the support set. -/
theorem Signs.mem_suppSet {v : D.Q.V} {s : Bool} {h h' : HWord D.Q} (hv : S.Valid v s h)
    (hv' : S.Valid v (!s) h') (hne : ¬ S.pnum M v s h h' ≤ S.pden M v s h h') :
    h ∈ S.suppSet M ∧ h' ∈ S.suppSet M := by
  refine ⟨⟨v, s, hv, lt_of_le_of_ne (S.minus_le_plus hv) fun e ↦ hne ?_⟩,
    ⟨v, !s, hv', lt_of_le_of_ne (S.minus_le_plus hv') fun e ↦ hne ?_⟩⟩
  · simp only [Signs.pnum, Signs.pden]; rw [← e]; exact le_sup_left
  · simp only [Signs.pnum, Signs.pden]; rw [← e]; exact le_sup_right

theorem csh_fin (L : List (Letter D.Q)) (f : ℕ → Letter D.Q) (n : ℕ) :
    ∃ L' : List (Letter D.Q), csh (.fin L) f n = .fin L' ∧ L'.length = L.length + n := by
  induction n with
  | zero => exact ⟨L, rfl, rfl⟩
  | succ n ih =>
      obtain ⟨L', h1, h2⟩ := ih
      refine ⟨(f n).inv :: L', ?_, by simp [h2]; omega⟩
      show (csh (.fin L) f n).cons (f n).inv = _
      rw [h1]; rfl

/-- **No mixed pairs**: a pair with one finite and one infinite side vanishes. -/
theorem Signs.le_of_inf_fin {v : D.Q.V} {s : Bool} {f : ℕ → Letter D.Q} {L : List (Letter D.Q)}
    (hv : S.Valid v s (.inf f)) (hv' : S.Valid v (!s) (.fin L)) :
    S.pnum M v s (.inf f) (.fin L) ≤ S.pden M v s (.inf f) (.fin L) := by
  by_contra hne
  have hmem : ∀ n, csh (.fin L) f n ∈ S.suppSet M := by
    intro n
    obtain ⟨h1, h2, h3⟩ := S.iter_shift M hv hv' n
    exact (S.mem_suppSet M h1 h2 (fun h ↦ hne (h3.mpr h))).2
  have hinj : Function.Injective (csh (.fin L) f) := by
    intro n m e
    obtain ⟨L1, e1, l1⟩ := csh_fin L f n
    obtain ⟨L2, e2, l2⟩ := csh_fin L f m
    rw [e1, e2] at e
    have := congrArg List.length (HWord.fin.inj e)
    omega
  exact Set.infinite_of_injective_forall_mem hinj hmem (S.suppSet_finite M)

omit [FiniteDimensional k M] in
theorem csh_inf (g f : ℕ → Letter D.Q) (n : ℕ) :
    csh (.inf g) f n = .inf fun t ↦ if t < n then (f (n - 1 - t)).inv else g (t - n) := by
  induction n with
  | zero => simp [csh]
  | succ n ih =>
      show (csh (.inf g) f n).cons (f n).inv = _
      rw [ih]
      simp only [HWord.cons, HWord.inf.injEq]
      funext t
      cases t with
      | zero => simp
      | succ t =>
          show (if t < n then (f (n - 1 - t)).inv else g (t - n)) = _
          by_cases h : t < n
          · rw [if_pos h, if_pos (by omega)]; congr 2; omega
          · rw [if_neg h, if_neg (by omega)]; congr 1; omega

omit [FiniteDimensional k M] in
theorem per_add_mul {f : ℕ → Letter D.Q} {p : ℕ} (hp : ∀ m, f (m + p) = f m) (m c : ℕ) :
    f (m + p * c) = f m := by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]

/-- **Periodicity**: a nonzero pair of infinite half-words is periodic, with the second
side the reversed inverse period. -/
theorem Signs.exists_min_period {v : D.Q.V} {s : Bool} {f g : ℕ → Letter D.Q}
    (hv : S.Valid v s (.inf f)) (hv' : S.Valid v (!s) (.inf g))
    (hne : ¬ S.pnum M v s (.inf f) (.inf g) ≤ S.pden M v s (.inf f) (.inf g)) :
    ∃ p, 0 < p ∧ (∀ m, f (m + p) = f m) ∧
      (∀ q, 0 < q → q < p → ¬ ∀ m, f (m + q) = f m) ∧
      ∀ u N, p ∣ N → u < N → g u = (f (N - 1 - u)).inv := by
  classical
  have hmem : ∀ n, ((HWord.inf fun i ↦ f (n + i)), csh (.inf g) f n) ∈
      S.suppSet M ×ˢ S.suppSet M := by
    intro n
    obtain ⟨h1, h2, h3⟩ := S.iter_shift M hv hv' n
    exact S.mem_suppSet M h1 h2 (fun h ↦ hne (h3.mpr h))
  obtain ⟨i, j, hij, e⟩ :=
    ((S.suppSet_finite M).prod (S.suppSet_finite M)).exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨eD, eC⟩ := Prod.mk.inj e
  have hD : ∀ t, f (i + t) = f (j + t) := fun t ↦ congrFun (HWord.inf.inj eD) t
  rw [csh_inf, csh_inf] at eC
  have hC := fun t ↦ congrFun (HWord.inf.inj eC) t
  set p := j - i with hp
  have hper : ∀ m, f (m + p) = f m := by
    intro m
    by_cases hm : i ≤ m
    · have := hD (m - i)
      rw [show i + (m - i) = m by omega, show j + (m - i) = m + p by omega] at this
      exact this.symm
    · have := hC (i - 1 - m)
      simp only [show i - 1 - m < i by omega, show i - 1 - m < j by omega, if_true] at this
      rw [show i - 1 - (i - 1 - m) = m by omega, show j - 1 - (i - 1 - m) = m + p by omega] at this
      have := congrArg Letter.inv this
      simp only [Letter.inv_inv'] at this
      exact this.symm
  have hg : ∀ u N, p ∣ N → u < N → g u = (f (N - 1 - u)).inv := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
        intro N hN hu
        obtain ⟨c, rfl⟩ := hN
        have := hC (i + u)
        simp only [show ¬ (i + u < i) by omega, if_false, Nat.add_sub_cancel_left] at this
        rw [this]
        by_cases hup : i + u < j
        · rw [if_pos hup]
          have hc : 1 ≤ c := by
            rcases Nat.eq_zero_or_pos c with h | h
            · subst h; simp at hu
            · exact h
          congr 1
          rw [show p * c - 1 - u = (j - 1 - (i + u)) + p * (c - 1) by
            rw [Nat.mul_sub, Nat.mul_one]
            have : p ≤ p * c := Nat.le_mul_of_pos_right p hc
            omega]
          exact (per_add_mul hper _ _).symm
        · rw [if_neg hup, ih (i + u - j) (by omega) (p * c) ⟨c, rfl⟩ (by omega)]
          congr 1
          rw [show p * c - 1 - (i + u - j) = (p * c - 1 - u) + p by omega, hper]
  -- the minimal period
  have hex : ∃ q, 0 < q ∧ ∀ m, f (m + q) = f m := ⟨p, by omega, hper⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun q hq hlt hq' ↦ Nat.find_min hex hlt ⟨hq, hq'⟩, fun u N hN hu ↦ ?_⟩
  set p0 := Nat.find hex
  have hper0 := (Nat.find_spec hex).2
  obtain ⟨c, rfl⟩ := hN
  have hp0 : 0 < p := by omega
  rw [hg u (p0 * c * p) (Dvd.intro_left _ rfl) (by
    calc u < p0 * c := hu
      _ ≤ p0 * c * p := Nat.le_mul_of_pos_right _ hp0)]
  congr 1
  have h1 : p0 * c * p = p0 * c + p0 * (c * (p - 1)) := by
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [hp', Nat.add_sub_cancel]; ring
  rw [show p0 * c * p - 1 - u = (p0 * c - 1 - u) + p0 * (c * (p - 1)) by
    rw [h1]
    generalize p0 * c = X at hu ⊢
    generalize p0 * (c * (p - 1)) = Y
    omega]
  exact per_add_mul hper0 _ _

end MonomialData

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
variable [FiniteDimensional k M]

include hA in
/-- A nonzero band pair functor forces the band to avoid zero paths. -/
theorem killsZero_of_ne (hne : ¬ b.numB S M b.first ≤ b.denB S M b.first) : b.KillsZero := by
  intro x l hz i hi
  by_contra hf
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hf
  obtain ⟨y, hyn, hyd⟩ := Set.not_subset.mp hne
  set m := b.n * l.length + i.val + l.length
  obtain ⟨z, hzn, hch⟩ := b.numB_ch S hA M (m := m) hyn
  obtain ⟨c, hc0, hcm, hcs⟩ := b.fun_of_ch M hch
  have hvsp : ∀ t ≤ m, c t ∈ D.vsp M (b.vtx (b.succ^[t] b.first)) := by
    intro t ht
    rcases Nat.lt_or_ge t m with h | h
    · exact (MonomialData.rel_vsp (hcs t h)).1
    · rw [show t = m by omega, hcm]
      exact S.plus_le_vsp (b.valid_rightW S hA _) hzn.1
  have key : ∀ (l : List D.Q.A) (i j : Fin b.n) (t : ℕ), b.followPos i l = some j →
      b.succ^[t] b.first = i → l.length ≤ t → t + l.length ≤ m →
      ∃ t' ≤ m, c t' = D.pval (b.vtx i) l • c t := by
    intro l
    induction l with
    | nil =>
        intro i j t _ ht _ hm
        refine ⟨t, by simpa using hm, ?_⟩
        have := hvsp t (by simpa using hm)
        rw [ht] at this
        exact ((D.mem_vsp).mp this).symm
    | cons a l ih =>
        intro i j t h ht hl1 hl2
        simp only [List.length_cons] at hl1 hl2
        simp only [followPos] at h
        cases hn : b.next a i with
        | none => rw [hn] at h; cases h
        | some j1 =>
            rw [hn] at h
            have hvi : b.vtx i = D.Q.src a := b.next_src a i j1 hn
            have hvj : b.vtx j1 = D.Q.tgt a := b.next_tgt a i j1 hn
            have hct : c t ∈ D.vsp M (b.vtx i) := by
              have := hvsp t (by omega); rwa [ht] at this
            have hstep : ∃ t1, b.succ^[t1] b.first = j1 ∧ l.length ≤ t1 ∧
                t1 + l.length ≤ m ∧ c t1 = D.α a • c t := by
              rcases (b.next_eq_some_iff S hA a i j1).mp hn with ⟨hl, rfl⟩ | ⟨hl, rfl⟩
              · refine ⟨t + 1, by rw [Function.iterate_succ_apply', ht], by omega, by omega, ?_⟩
                have hr := hcs t (by omega)
                rw [ht, hl] at hr
                simp only [MonomialData.Rel, if_true] at hr
                exact hr.2
              · have ht1 : b.succ^[t - 1] b.first = b.pred i := by
                  rw [← eq_succ_iff]
                  have e := Function.iterate_succ_apply' b.succ (t - 1) b.first
                  rw [show (t - 1).succ = t by omega, ht] at e
                  exact e
                refine ⟨t - 1, ht1, by omega, by omega, ?_⟩
                have hr := hcs (t - 1) (by omega)
                rw [ht1, hl, show t - 1 + 1 = t by omega] at hr
                simp only [MonomialData.Rel, Bool.false_eq_true, if_false] at hr
                exact hr.2
            obtain ⟨t1, ht1, hb1, hb2, hc1⟩ := hstep
            obtain ⟨t', ht', hc'⟩ := ih j1 j t1 h ht1 hb1 hb2
            refine ⟨t', ht', ?_⟩
            rw [hc', hc1, hvj]
            change _ = (D.pval (D.Q.tgt a) l * D.α a * D.e (b.vtx i)) • c t
            rw [mul_smul, mul_smul, (D.mem_vsp).mp hct]
  have hti : b.succ^[b.n * l.length + i.val] b.first = i := by
    ext
    rw [iter_succ_val]
    show (0 + (b.n * l.length + i.val)) % b.n = i.val
    rw [Nat.zero_add, Nat.mul_add_mod, Nat.mod_eq_of_lt i.2]
  obtain ⟨t', ht', hc'⟩ := key l i j _ hj hti
    (by have := b.n_pos; nlinarith) le_rfl
  rw [hi, hz, zero_smul] at hc'
  apply hyd
  refine Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨?_, hyn.2⟩)
  refine (b.mem_minus_right S M).mpr ⟨t', ?_⟩
  have := b.ch_of_fun M c (p := b.first) (i := 0) (m := t') (fun q _ hq ↦ hcs q (by omega))
  simpa [hc0, hc'] using this

/-- The band on the first `n` letters of an infinite word. -/
def ofPer (v : D.Q.V) (f : ℕ → Letter D.Q) (n : ℕ) (hn : 0 < n)
    (hw : D.Q.IsWalk v (List.ofFn fun i : Fin n ↦ f i))
    (hc : D.Q.wend v (List.ofFn fun i : Fin n ↦ f i) = v) : CWord D.Q :=
  ⟨v, List.ofFn fun i : Fin n ↦ f i, by rw [Ne, List.ofFn_eq_nil_iff]; omega, hw, hc⟩

section ofPer

variable {v : D.Q.V} {f : ℕ → Letter D.Q} {n : ℕ} {hn : 0 < n}
  {hw : D.Q.IsWalk v (List.ofFn fun i : Fin n ↦ f i)}
  {hc : D.Q.wend v (List.ofFn fun i : Fin n ↦ f i) = v}

omit [FiniteDimensional k M] in
theorem ofPer_n : (ofPer v f n hn hw hc).n = n := List.length_ofFn

omit [FiniteDimensional k M] in
theorem ofPer_lt (i : Fin (ofPer v f n hn hw hc).n) : (ofPer v f n hn hw hc).lt i = f i.val := by
  simp [lt, ofPer]

omit [FiniteDimensional k M] in
theorem per_mod (hper : ∀ m, f (m + n) = f m) (m : ℕ) : f (m % n) = f m := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  exact (MonomialData.per_add_mul hper _ _).symm

omit [FiniteDimensional k M] in
theorem ofPer_lt_iter (hper : ∀ m, f (m + n) = f m) (p : Fin (ofPer v f n hn hw hc).n) (t : ℕ) :
    (ofPer v f n hn hw hc).lt ((ofPer v f n hn hw hc).succ^[t] p) = f (p.val + t) := by
  rw [ofPer_lt, iter_succ_val]
  exact per_mod (n := (ofPer v f n hn hw hc).n) (by rw [ofPer_n]; exact hper) _

end ofPer

/-- **Realization of infinite pairs**: a nonzero pair of infinite half-words is the pair at
the first position of a primitive band without zero paths. -/
theorem exists_band {v : D.Q.V} {s : Bool} {f g : ℕ → Letter D.Q}
    (hv : S.Valid v s (.inf f)) (hv' : S.Valid v (!s) (.inf g))
    (hne : ¬ S.pnum M v s (.inf f) (.inf g) ≤ S.pden M v s (.inf f) (.inf g)) :
    ∃ (b : CWord D.Q) (hA : b.Alt S), b.KillsZero ∧
      (∀ p q, b.rightW p = b.rightW q → p = q) ∧
      b.vtx b.first = v ∧ S.st (b.lt b.first) = s ∧ b.rightW b.first = f ∧
      b.leftW b.first = g := by
  obtain ⟨n, hn, hper, hmin, hg⟩ := S.exists_min_period M hv hv' hne
  obtain ⟨h0, hs0, hf⟩ := S.valid_inf_facts hv
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
  have hRf : b.rightW b.first = f := by rw [hR]; funext t; simp [first]
  have hLg : b.leftW b.first = g := by
    funext t
    simp only [leftW]
    rw [ofPer_lt, hg t (n * (t + 1)) (Dvd.intro _ rfl) (by nlinarith)]
    congr 1
    set r := ((b.pred^[t + 1]) b.first).val
    have h1 : (r + (t + 1)) % n = 0 := by
      have := congrArg Fin.val (b.iter_succ_pred b.first (t + 1))
      rw [iter_succ_val] at this
      change (r + (t + 1)) % b.n = 0 at this
      rwa [hbn] at this
    have h2 : (n * (t + 1) - 1 - t + (t + 1)) % n = 0 := by
      rw [show n * (t + 1) - 1 - t + (t + 1) = n * (t + 1) by
        have : t + 1 ≤ n * (t + 1) := Nat.le_mul_of_pos_left _ hn
        omega]
      simp
    have hmod : r % n = (n * (t + 1) - 1 - t) % n :=
      Nat.ModEq.add_right_cancel' (t + 1) (h1.trans h2.symm)
    rw [← per_mod hper r, hmod, per_mod hper]
  have hvf : b.vtx b.first = v := by
    show (b.lt b.first).src = v
    rw [ofPer_lt]; exact h0
  have hsf : S.st (b.lt b.first) = s := by rw [ofPer_lt]; exact hs0
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
  refine ⟨b, hA, b.killsZero_of_ne S hA M ?_, hprim, hvf, hsf, hRf, hLg⟩
  rw [numB_eq_pnum, denB, hvf, hsf, hRf, hLg]
  exact hne

end CWord

end BrickAccessibility
