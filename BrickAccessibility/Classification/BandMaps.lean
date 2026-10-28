module

public import BrickAccessibility.Classification.BandRel
public import BrickAccessibility.Classification.BlockMaps

/-!
# Maps from band modules

Let `ι : V → M` land in the numerator at the first position of a band `b`, and let
`φ` be an automorphism of `V` such that `ι y` is joined to `ι (φ y)` by a chain
along one period. Then a linear choice of such chains gives a module map from
the band module `M(b, V, φ)` to `M` restricting to `ι` on the block at the first
position (`exists_bandHom`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace MonomialData

variable {D : MonomialData k B} {M : Type*} [AddCommGroup M] [Module B M] [Module k M]
  [IsScalarTower k B M]

/-- An arrow with the sign of a letter at its start kills `l^* U`, unless the
letter is that arrow. -/
theorem Signs.α_smul_eq_zero_of_mem_tr (S : D.Signs) {l : Letter D.Q} {a : D.Q.A}
    (hsrc : D.Q.src a = l.src) (hσ : S.σ a = S.st l) (hl : l ≠ (a, true))
    {U : Submodule k M} {x : M} (hx : x ∈ D.tr l U) : D.α a • x = 0 := by
  obtain ⟨b, d⟩ := l
  cases d
  · simp only [Letter.src, Bool.false_eq_true, if_false] at hsrc
    simp only [Signs.st_false] at hσ
    obtain ⟨y, -, -, rfl⟩ := (D.mem_tr_false).mp hx
    exact α_smul_α_smul_eq_zero hsrc.symm (fun h ↦ S.hall b a h hσ) y
  · exfalso
    simp only [Letter.src, if_true] at hsrc
    simp only [Signs.st_true] at hσ
    have : b = a := by
      by_contra hne
      exact S.hσ b a hne hsrc.symm hσ.symm
    subst this
    exact hl rfl

end MonomialData

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

theorem iter_first (q : ℕ) (hq : q < b.n) : b.succ^[q] b.first = ⟨q, hq⟩ :=
  Fin.ext (by rw [iter_succ_val]; show (0 + q) % b.n = q; rw [Nat.zero_add, Nat.mod_eq_of_lt hq])

/-- A function chain gives a chain. -/
theorem ch_of_fun {p : Fin b.n} (c : ℕ → M) {i m : ℕ}
    (h : ∀ q, i ≤ q → q < i + m → MonomialData.Rel (b.lt (b.succ^[q] p)) (c q) (c (q + 1))) :
    b.Ch M (b.succ^[i] p) m (c i) (c (i + m)) := by
  induction m generalizing i with
  | zero => exact (ch_zero_len b M).mpr rfl
  | succ m ih =>
      refine ⟨c (i + 1), h i le_rfl (by omega), ?_⟩
      have := ih (i := i + 1) (fun q h1 h2 ↦ h q (by omega) (by omega))
      rw [Function.iterate_succ_apply'] at this
      rwa [show i + (m + 1) = i + 1 + m by omega]

/-- A chain as a function. -/
theorem fun_of_ch {p : Fin b.n} {m : ℕ} {x y : M} (h : b.Ch M p m x y) :
    ∃ c : ℕ → M, c 0 = x ∧ c m = y ∧
      ∀ q < m, MonomialData.Rel (b.lt (b.succ^[q] p)) (c q) (c (q + 1)) := by
  induction m generalizing p x with
  | zero => exact ⟨fun _ ↦ x, rfl, (ch_zero_len b M).mp h, fun q hq ↦ absurd hq (Nat.not_lt_zero _)⟩
  | succ m ih =>
      obtain ⟨z, hz, hr⟩ := h
      obtain ⟨c, h0, hm, hs⟩ := ih hr
      refine ⟨fun q ↦ match q with | 0 => x | q + 1 => c q, rfl, hm, fun q hq ↦ ?_⟩
      cases q with
      | zero => simpa [h0] using hz
      | succ q =>
          have := hs q (by omega)
          rwa [← Function.iterate_succ_apply] at this

/-- The space of function chains along one period from `p`. -/
def chW (p : Fin b.n) : Submodule k (ℕ → M) where
  carrier := {c | ∀ q < b.n, MonomialData.Rel (b.lt (b.succ^[q] p)) (c q) (c (q + 1))}
  add_mem' h h' q hq := MonomialData.rel_add (h q hq) (h' q hq)
  zero_mem' q _ := MonomialData.rel_zero _
  smul_mem' c _ h q hq := MonomialData.rel_smul c (h q hq)

variable {M} {V : Type*} [AddCommGroup V] [Module k V]

/-- A linear choice of chains joining `ι y` to `ι (φ y)`. -/
theorem exists_chain_lift (p : Fin b.n) (ι : V →ₗ[k] M) (φ : V →ₗ[k] V)
    (hch : ∀ y, b.Ch M p b.n (ι y) (ι (φ y))) :
    ∃ σ : V →ₗ[k] b.chW M p, ∀ y, (σ y).1 0 = ι y ∧ (σ y).1 b.n = ι (φ y) := by
  let ev : b.chW M p →ₗ[k] M × M :=
    ((LinearMap.proj 0).comp (b.chW M p).subtype).prod
      ((LinearMap.proj b.n).comp (b.chW M p).subtype)
  let f : V →ₗ[k] M × M := ι.prod (ι.comp φ)
  have hg : ∀ y, f y ∈ LinearMap.range ev := by
    intro y
    obtain ⟨c, h0, hn, hs⟩ := b.fun_of_ch M (hch y)
    exact ⟨⟨c, hs⟩, Prod.ext h0 hn⟩
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property ev.rangeRestrict
    (f.codRestrict _ hg) (LinearMap.surjective_rangeRestrict _)
  refine ⟨σ, fun y ↦ ?_⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem iter_first_eq (i : Fin b.n) : b.succ^[i.val] b.first = i := by
  rw [b.iter_first i.val i.2]

theorem last_val_succ : b.last.val + 1 = b.n := by
  have := b.n_pos; simp only [last]; omega

include hA in
/-- Arrows without a move kill the numerator at a band position. -/
theorem kill_numB [FiniteDimensional k M] {i : Fin b.n} {a : D.Q.A} (h : b.next a i = none)
    {x : M} (hx : x ∈ b.numB S M i) : D.α a • x = 0 := by
  have hvR := b.valid_rightW S hA i
  have hvL := b.valid_leftW S hA i
  by_cases hsrc : D.Q.src a = b.vtx i
  · by_cases hσ : S.σ a = S.st (b.lt i)
    · have h1 := (S.plus_le_pre hvR (i := 0) (l := b.lt i) (by simp [HWord.pre, rightW])).1 hx.1
      simp only [HWord.pre, List.ofFn_zero, List.nil_append, MonomialData.trs_cons,
        MonomialData.trs_nil] at h1
      refine S.α_smul_eq_zero_of_mem_tr hsrc hσ (fun hl ↦ ?_) h1
      have := (b.next_eq_some_iff S hA a i (b.succ i)).mpr (Or.inl ⟨hl, rfl⟩)
      rw [h] at this; cases this
    · have hσ' : S.σ a = !S.st (b.lt i) := Bool.eq_not_iff.mpr hσ
      have h1 := (S.plus_le_pre hvL (i := 0) (l := (b.lt (b.pred i)).inv)
        (by simp [HWord.pre, leftW])).1 hx.2
      simp only [HWord.pre, List.ofFn_zero, List.nil_append, MonomialData.trs_cons,
        MonomialData.trs_nil] at h1
      refine S.α_smul_eq_zero_of_mem_tr
        (by rw [Letter.src_inv, b.lt_tgt, succ_pred]; exact hsrc)
        (by rw [MonomialData.Signs.st_inv, b.en_pred S hA]; exact hσ') (fun hl ↦ ?_) h1
      have hl' : b.lt (b.pred i) = (a, false) := by
        rw [← Letter.inv_inv' (b.lt (b.pred i)), hl]; rfl
      have := (b.next_eq_some_iff S hA a i (b.pred i)).mpr (Or.inr ⟨hl', rfl⟩)
      rw [h] at this; cases this
  · exact D.α_smul_of_mem_vsp (Ne.symm hsrc) (S.plus_le_vsp hvR hx.1)

include hA in
/-- Values of a chain from the first position lie in the numerators. -/
theorem mem_numB_of_chW [FiniteDimensional k M] {c : ℕ → M} (hc : c ∈ b.chW M b.first)
    (h0 : c 0 ∈ b.numB S M b.first) (hn : c b.n ∈ b.numB S M b.first) (i : Fin b.n) :
    c i.val ∈ b.numB S M i := by
  constructor
  · have h2 := b.ch_of_fun M c (p := b.first) (i := i.val) (m := b.n - i.val)
      (fun q _ h2 ↦ hc q (by omega))
    rw [b.iter_first_eq, show i.val + (b.n - i.val) = b.n by omega] at h2
    refine b.PR_of_ch S hA M h2 ?_
    have e2 : b.succ^[b.n - i.val] i = b.first := Fin.ext (by
      rw [iter_succ_val, show i.val + (b.n - i.val) = b.n by omega, Nat.mod_self]; rfl)
    rw [e2]; exact hn.1
  · have h1 := b.ch_of_fun M c (p := b.first) (i := 0) (m := i.val)
      (fun q _ h2 ↦ hc q (by omega))
    simp only [Function.iterate_zero, id, Nat.zero_add] at h1
    have := b.PL_of_ch S hA M h1 h0.2
    rwa [b.iter_first_eq] at this

variable {V : Type u} [AddCommGroup V] [Module k V]

include hA in
theorem band_move [FiniteDimensional k M] (ι : V →ₗ[k] M) (φ : V ≃ₗ[k] V)
    (hι : ∀ y, ι y ∈ b.numB S M b.first) (σ : V →ₗ[k] b.chW M b.first)
    (hσ : ∀ y, (σ y).1 0 = ι y ∧ (σ y).1 b.n = ι (φ y)) (a : D.Q.A) (i j : Fin b.n) (y : V)
    (h : b.next a i = some j) :
    D.α a • (σ y).1 i.val = (σ ((b.blockQuiver S hA V φ).g a i y)).1 j.val := by
  show D.α a • (σ y).1 i.val = (σ ((b.blockQuiver S hA V φ).g a i y)).1 j.val
  change b.next a i = some j at h
  rcases (b.next_eq_some_iff S hA a i j).mp h with ⟨hl, rfl⟩ | ⟨hl, rfl⟩
  · have hr := (σ y).2 i.val i.2
    rw [b.iter_first_eq, hl] at hr
    simp only [MonomialData.Rel, if_true] at hr
    by_cases hi : i.val + 1 < b.n
    · have h1 : ¬ (i = b.last ∧ b.lt b.last = (a, true)) := fun h' ↦ by
        have := congrArg Fin.val h'.1; simp only [last] at this; omega
      have h2 : ¬ (i = b.first ∧ b.lt b.last = (a, false)) := by
        rintro ⟨rfl, h2⟩
        exact b.not_fork S hA b.last a false h2 (by rw [succ_last]; exact hl)
      have hg : (b.blockQuiver S hA V φ).g a i y = y := by
        simp only [blockQuiver, if_neg h1, if_neg h2]; rfl
      rw [hg, b.succ_val_of_lt i hi]
      exact hr.2.symm
    · have hil : i = b.last := Fin.ext (by simp only [last]; omega)
      subst hil
      have hg : (b.blockQuiver S hA V φ).g a b.last y = φ y := by
        simp [blockQuiver, hl]
      rw [hg, succ_last]
      show _ = (σ (φ y)).1 0
      rw [b.last_val_succ, (hσ y).2] at hr
      rw [(hσ (φ y)).1]
      exact hr.2.symm
  · have hni : b.lt i ≠ (a, true) := fun h' ↦
      b.not_fork S hA (b.pred i) a false hl (by rw [succ_pred]; exact h')
    by_cases hi : i.val = 0
    · have hif : i = b.first := Fin.ext hi
      subst hif
      rw [pred_first] at hl ⊢
      have h1 : ¬ (b.first = b.last ∧ b.lt b.last = (a, true)) := by
        rintro ⟨-, h'⟩; rw [hl] at h'; simp at h'
      have hg : (b.blockQuiver S hA V φ).g a b.first y = φ.symm y := by
        simp [blockQuiver, hl]
      rw [hg]
      show D.α a • (σ y).1 0 = _
      have hr := (σ (φ.symm y)).2 b.last.val b.last.2
      rw [b.iter_first_eq, hl, b.last_val_succ, (hσ _).2, φ.apply_symm_apply] at hr
      simp only [MonomialData.Rel, Bool.false_eq_true, if_false] at hr
      rw [(hσ y).1]
      exact hr.2.symm
    · have hp : (b.pred i).val + 1 = i.val := by
        rw [b.pred_val_of_pos i (by omega)]; omega
      have h1 : ¬ (i = b.last ∧ b.lt b.last = (a, true)) := by
        rintro ⟨rfl, h'⟩; exact hni h'
      have h2 : ¬ (i = b.first ∧ b.lt b.last = (a, false)) := by
        rintro ⟨rfl, -⟩; exact hi rfl
      have hg : (b.blockQuiver S hA V φ).g a i y = y := by
        simp only [blockQuiver, if_neg h1, if_neg h2]; rfl
      rw [hg]
      have hr := (σ y).2 (b.pred i).val (b.pred i).2
      rw [b.iter_first_eq, hl, hp] at hr
      simp only [MonomialData.Rel, Bool.false_eq_true, if_false] at hr
      exact hr.2.symm

include hA in
/-- The compatible family on `M(b, V, φ)` given by a chain lift. -/
def bandCompat [FiniteDimensional k M] (ι : V →ₗ[k] M) (φ : V ≃ₗ[k] V)
    (hι : ∀ y, ι y ∈ b.numB S M b.first) (σ : V →ₗ[k] b.chW M b.first)
    (hσ : ∀ y, (σ y).1 0 = ι y ∧ (σ y).1 b.n = ι (φ y)) :
    (b.blockQuiver S hA V φ).Compat M where
  ψ i := (LinearMap.proj (R := k) (φ := fun _ : ℕ ↦ M) i.val).comp
    ((b.chW M b.first).subtype.comp σ)
  mem_vsp j y := by
    have := b.mem_numB_of_chW S hA (σ y).2 (by rw [(hσ y).1]; exact hι y)
      (by rw [(hσ y).2]; exact hι (φ y)) j
    exact S.plus_le_vsp (b.valid_rightW S hA j) this.1
  move a i j y h := b.band_move S hA ι φ hι σ hσ a i j y h
  kill a i y h := by
    show D.α a • (σ y).1 i.val = 0
    exact b.kill_numB S hA h (b.mem_numB_of_chW S hA (σ y).2
      (by rw [(hσ y).1]; exact hι y) (by rw [(hσ y).2]; exact hι (φ y)) i)

include hA in
/-- **Maps from band modules.** -/
theorem exists_bandHom [FiniteDimensional k M] (hK : b.KillsZero) (ι : V →ₗ[k] M)
    (φ : V ≃ₗ[k] V) (hι : ∀ y, ι y ∈ b.numB S M b.first)
    (hch : ∀ y, b.Ch M b.first b.n (ι y) (ι (φ y))) :
    ∃ Θ : (b.blockQuiver S hA V φ).Mod (b.blockQuiver_kills S hA hK V φ) →ₗ[B] M,
      (∀ y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single b.first y)) = ι y) ∧
      (∀ q y, Θ (MonomialData.BlockQuiver.ofFun _ _ (Pi.single q y)) ∈ b.numB S M q) := by
  obtain ⟨σ, hσ⟩ := b.exists_chain_lift b.first ι φ.toLinearMap hch
  let F := b.bandCompat S hA ι φ hι σ hσ
  refine ⟨F.toHom _, fun y ↦ ?_, fun q y ↦ ?_⟩
  · exact (F.toHom_single (b.blockQuiver_kills S hA hK V φ) b.first y).trans (hσ y).1
  · have e := F.toHom_single (b.blockQuiver_kills S hA hK V φ) q y
    refine (congrArg (fun x ↦ x ∈ b.numB S M q) e).mpr ?_
    exact b.mem_numB_of_chW S hA (σ y).2 (by rw [(hσ y).1]; exact hι y)
      (by rw [(hσ y).2]; exact hι (φ y)) q

end CWord

end BrickAccessibility
