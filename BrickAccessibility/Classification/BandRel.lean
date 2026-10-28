module

public import BrickAccessibility.Classification.BandWalks
public import BrickAccessibility.Classification.BandSplit
public import BrickAccessibility.Classification.Chains

/-!
# The band relation in a module

For a band `b` and a finite-dimensional module `M`, the half-words at position
`p` satisfy `h⁺_R(p) = l_p^*(h⁺_R(p+1))` and `h⁺_L(p+1) = (l_p⁻¹)^*(h⁺_L(p))`.
The band relation `R` (chains along one period) has full domain and range on
the numerator at a position, so the splitting lemma applies.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement Module

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace CWord

variable {D : MonomialData k B} (S : D.Signs) (b : CWord D.Q) (hA : b.Alt S)
variable (M : Type*) [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

theorem rightW_cons (p : Fin b.n) :
    HWord.inf (b.rightW p) = (HWord.inf (b.rightW (b.succ p))).cons (b.lt p) := by
  simp only [HWord.cons, HWord.inf.injEq]
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [rightW, Function.iterate_succ_apply]

theorem leftW_cons (p : Fin b.n) :
    HWord.inf (b.leftW (b.succ p)) = (HWord.inf (b.leftW p)).cons (b.lt p).inv := by
  simp only [HWord.cons, HWord.inf.injEq]
  funext i
  cases i with
  | zero => simp [leftW]
  | succ i =>
      simp only [leftW]
      rw [Function.iterate_succ_apply, pred_succ]

theorem iter_succ_val (p : Fin b.n) (i : ℕ) : (b.succ^[i] p).val = (p.val + i) % b.n := by
  induction i with
  | zero => simp [Nat.mod_eq_of_lt p.2]
  | succ i ih =>
      rw [Function.iterate_succ_apply',
        show (b.succ (b.succ^[i] p)).val = ((b.succ^[i] p).val + 1) % b.n from rfl, ih,
        Nat.mod_add_mod, Nat.add_assoc]

theorem iter_succ_mul (p : Fin b.n) (j : ℕ) : b.succ^[j * b.n] p = p := by
  ext; rw [iter_succ_val, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2]

theorem iter_succ_n (p : Fin b.n) : b.succ^[b.n] p = p := by
  simpa using b.iter_succ_mul p 1

theorem iter_succ_pred (q : Fin b.n) (m : ℕ) : b.succ^[m] (b.pred^[m] q) = q := by
  induction m generalizing q with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply', succ_pred, ih]

theorem iter_pred_mul (p : Fin b.n) (j : ℕ) : b.pred^[j * b.n] p = p := by
  conv_rhs => rw [← b.iter_succ_pred p (j * b.n)]
  rw [b.iter_succ_mul]

/-- Chains of length `m` along the band, starting at position `p`. -/
def Ch : Fin b.n → ℕ → M → M → Prop
  | _, 0, x, y => x = y
  | p, m + 1, x, y => ∃ z, MonomialData.Rel (b.lt p) x z ∧ Ch (b.succ p) m z y

theorem ch_zero_len {p : Fin b.n} {x y : M} : b.Ch M p 0 x y ↔ x = y := Iff.rfl

theorem ch_append {p : Fin b.n} {m m' : ℕ} {x y z : M} (h : b.Ch M p m x y)
    (h' : b.Ch M (b.succ^[m] p) m' y z) : b.Ch M p (m + m') x z := by
  induction m generalizing p x with
  | zero =>
      have : x = y := h
      subst this
      simpa using h'
  | succ m ih =>
      obtain ⟨w, hw, hrest⟩ := h
      rw [show m + 1 + m' = (m + m') + 1 by omega]
      exact ⟨w, hw, ih hrest (by rwa [Function.iterate_succ_apply] at h')⟩

theorem ch_split {p : Fin b.n} {m m' : ℕ} {x z : M} (h : b.Ch M p (m + m') x z) :
    ∃ y, b.Ch M p m x y ∧ b.Ch M (b.succ^[m] p) m' y z := by
  induction m generalizing p x with
  | zero => exact ⟨x, (ch_zero_len b M).mpr rfl, by simpa using h⟩
  | succ m ih =>
      rw [show m + 1 + m' = (m + m') + 1 by omega] at h
      obtain ⟨w, hw, hrest⟩ := h
      obtain ⟨y, h1, h2⟩ := ih hrest
      exact ⟨y, ⟨w, hw, h1⟩, by rwa [Function.iterate_succ_apply]⟩

theorem ch_succ_right {p : Fin b.n} {m : ℕ} {x y : M} :
    b.Ch M p (m + 1) x y ↔ ∃ z, b.Ch M p m x z ∧ MonomialData.Rel (b.lt (b.succ^[m] p)) z y := by
  constructor
  · intro h
    obtain ⟨z, h1, w, hw, hwy⟩ := b.ch_split M h
    exact ⟨z, h1, (show w = y from hwy) ▸ hw⟩
  · rintro ⟨z, h1, hz⟩
    exact b.ch_append M h1 ⟨y, hz, (ch_zero_len b M).mpr rfl⟩

theorem ch_zero (p : Fin b.n) (m : ℕ) : b.Ch M p m 0 0 := by
  induction m generalizing p with
  | zero => exact (ch_zero_len b M).mpr rfl
  | succ m ih => exact ⟨0, MonomialData.rel_zero _, ih _⟩

theorem ch_add {p : Fin b.n} {m : ℕ} {x y x' y' : M} (h : b.Ch M p m x y)
    (h' : b.Ch M p m x' y') : b.Ch M p m (x + x') (y + y') := by
  induction m generalizing p x x' with
  | zero =>
      have e : x = y := h
      have e' : x' = y' := h'
      exact (ch_zero_len b M).mpr (by rw [e, e'])
  | succ m ih =>
      obtain ⟨z, hz, hr⟩ := h
      obtain ⟨z', hz', hr'⟩ := h'
      exact ⟨z + z', MonomialData.rel_add hz hz', ih hr hr'⟩

theorem ch_smul {p : Fin b.n} {m : ℕ} {x y : M} (c : k) (h : b.Ch M p m x y) :
    b.Ch M p m (c • x) (c • y) := by
  induction m generalizing p x with
  | zero =>
      have e : x = y := h
      exact (ch_zero_len b M).mpr (by rw [e])
  | succ m ih =>
      obtain ⟨z, hz, hr⟩ := h
      exact ⟨c • z, MonomialData.rel_smul c hz, ih hr⟩

/-- Padding a chain to `0` by zeros. -/
theorem ch_pad {p : Fin b.n} {m m' : ℕ} {x : M} (h : b.Ch M p m x 0) (hm : m ≤ m') :
    b.Ch M p m' x 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact b.ch_append M h (b.ch_zero M _ r)

/-- Padding a chain from `0` by zeros in front. -/
theorem ch_pad_left {p : Fin b.n} {m r : ℕ} {x : M} (h : b.Ch M (b.pred^[m] p) m 0 x) :
    b.Ch M (b.pred^[r + m] p) (r + m) 0 x := by
  refine b.ch_append M (b.ch_zero M _ r) ?_
  rwa [Function.iterate_add_apply, b.iter_succ_pred]

theorem ch_trs {p : Fin b.n} {m : ℕ} {x : M} {U : Submodule k M} :
    x ∈ D.trs (List.ofFn fun i : Fin m ↦ b.rightW p i) U ↔ ∃ y ∈ U, b.Ch M p m x y := by
  induction m generalizing p x with
  | zero => simp [ch_zero_len]
  | succ m ih =>
      have e : (List.ofFn fun i : Fin (m + 1) ↦ b.rightW p i) =
          b.lt p :: List.ofFn fun i : Fin m ↦ b.rightW (b.succ p) i := by
        rw [List.ofFn_succ]
        simp [rightW, Function.iterate_succ_apply]
      rw [e, MonomialData.trs_cons, MonomialData.mem_tr_iff]
      constructor
      · rintro ⟨z, hz, hzU⟩
        obtain ⟨y, hy, hch⟩ := ih.mp hzU
        exact ⟨y, hy, z, hz, hch⟩
      · rintro ⟨y, hy, z, hz, hch⟩
        exact ⟨z, hz, ih.mpr ⟨y, hy, hch⟩⟩

theorem ch_trs_left {p : Fin b.n} {m : ℕ} {x : M} {U : Submodule k M} :
    x ∈ D.trs (List.ofFn fun i : Fin m ↦ b.leftW p i) U ↔
      ∃ y ∈ U, b.Ch M (b.pred^[m] p) m y x := by
  induction m generalizing p x with
  | zero => simp [ch_zero_len, eq_comm]
  | succ m ih =>
      have e : (List.ofFn fun i : Fin (m + 1) ↦ b.leftW p i) =
          (b.lt (b.pred p)).inv :: List.ofFn fun i : Fin m ↦ b.leftW (b.pred p) i := by
        rw [List.ofFn_succ]
        simp [leftW, Function.iterate_succ_apply]
      have hq : b.pred^[m + 1] p = b.pred^[m] (b.pred p) := Function.iterate_succ_apply _ _ _
      have hs : b.succ^[m] (b.pred^[m] (b.pred p)) = b.pred p := b.iter_succ_pred _ _
      rw [e, MonomialData.trs_cons, MonomialData.mem_tr_iff, hq]
      constructor
      · rintro ⟨z, hz, hzU⟩
        obtain ⟨y, hy, hch⟩ := ih.mp hzU
        refine ⟨y, hy, (b.ch_succ_right M).mpr ⟨z, hch, ?_⟩⟩
        rw [hs]; exact (MonomialData.rel_inv _ _ _).mp hz
      · rintro ⟨y, hy, hch⟩
        obtain ⟨z, h1, h2⟩ := (b.ch_succ_right M).mp hch
        rw [hs] at h2
        exact ⟨z, (MonomialData.rel_inv _ _ _).mpr h2, ih.mpr ⟨y, hy, h1⟩⟩

theorem mem_minus_right {p : Fin b.n} {x : M} :
    x ∈ S.minus M (b.vtx p) (S.st (b.lt p)) (.inf (b.rightW p)) ↔ ∃ m, b.Ch M p m x 0 := by
  have hmono : Monotone fun m ↦
      D.trs (List.ofFn fun i : Fin m ↦ b.rightW p i) (⊥ : Submodule k M) := by
    refine monotone_nat_of_le_succ fun m y hy ↦ ?_
    obtain ⟨z, hz, hch⟩ := (b.ch_trs M).mp hy
    rw [(Submodule.mem_bot k).mp hz] at hch
    exact (b.ch_trs M).mpr ⟨0, Submodule.zero_mem _, b.ch_pad M hch (Nat.le_succ m)⟩
  change x ∈ (⨆ m, D.trs (List.ofFn fun i : Fin m ↦ b.rightW p i) ⊥) ↔ _
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  simp only [b.ch_trs M, Submodule.mem_bot, exists_eq_left]

theorem mem_minus_left {p : Fin b.n} {x : M} :
    x ∈ S.minus M (b.vtx p) (!S.st (b.lt p)) (.inf (b.leftW p)) ↔
      ∃ m, b.Ch M (b.pred^[m] p) m 0 x := by
  have hmono : Monotone fun m ↦
      D.trs (List.ofFn fun i : Fin m ↦ b.leftW p i) (⊥ : Submodule k M) := by
    refine monotone_nat_of_le_succ fun m y hy ↦ ?_
    obtain ⟨z, hz, hch⟩ := (b.ch_trs_left M).mp hy
    rw [(Submodule.mem_bot k).mp hz] at hch
    refine (b.ch_trs_left M).mpr ⟨0, Submodule.zero_mem _, ?_⟩
    rw [add_comm m 1]
    exact b.ch_pad_left M hch
  change x ∈ (⨆ m, D.trs (List.ofFn fun i : Fin m ↦ b.leftW p i) ⊥) ↔ _
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  simp only [b.ch_trs_left M, Submodule.mem_bot, exists_eq_left]

include hA

theorem st_succ (p : Fin b.n) : S.st (b.lt (b.succ p)) = !S.en (b.lt p) := by
  have := hA p
  revert this
  cases S.st (b.lt (b.succ p)) <;> cases S.en (b.lt p) <;> simp

variable [FiniteDimensional k M]

theorem plus_rightW (p : Fin b.n) :
    S.plus M (b.vtx p) (S.st (b.lt p)) (.inf (b.rightW p)) =
      D.tr (b.lt p) (S.plus M (b.vtx (b.succ p)) (S.st (b.lt (b.succ p)))
        (.inf (b.rightW (b.succ p)))) := by
  rw [b.rightW_cons p]
  have hv := b.valid_rightW S hA (b.succ p)
  rw [← b.lt_tgt, b.st_succ S hA] at hv
  rw [S.plus_cons (v := b.vtx p) rfl hv, b.lt_tgt, b.st_succ S hA]

theorem plus_leftW (p : Fin b.n) :
    S.plus M (b.vtx (b.succ p)) (!S.st (b.lt (b.succ p))) (.inf (b.leftW (b.succ p))) =
      D.tr (b.lt p).inv (S.plus M (b.vtx p) (!S.st (b.lt p)) (.inf (b.leftW p))) := by
  rw [b.leftW_cons p]
  have hv := b.valid_leftW S hA p
  have e1 : (b.lt p).inv.tgt = b.vtx p := by simp [vtx]
  have e2 : (!S.en (b.lt p).inv) = !S.st (b.lt p) := by rw [MonomialData.Signs.en_inv]
  rw [← e1, ← e2] at hv
  have e3 : (b.lt p).inv.src = b.vtx (b.succ p) := by simp [b.lt_tgt]
  rw [S.plus_cons e3 hv, e1, e2]

/-- `h⁺` of the rightward half at `p`. -/
def PR (p : Fin b.n) : Submodule k M := S.plus M (b.vtx p) (S.st (b.lt p)) (.inf (b.rightW p))

/-- `h⁺` of the leftward half at `p`. -/
def PL (p : Fin b.n) : Submodule k M :=
  S.plus M (b.vtx p) (!S.st (b.lt p)) (.inf (b.leftW p))

/-- The numerator of the band pair functor at `p`. -/
def numB (p : Fin b.n) : Submodule k M := b.PR S M p ⊓ b.PL S M p

/-- The denominator of the band pair functor at `p`. -/
def denB (p : Fin b.n) : Submodule k M :=
  S.pden M (b.vtx p) (S.st (b.lt p)) (.inf (b.rightW p)) (.inf (b.leftW p))

omit hA [FiniteDimensional k M] in
theorem numB_eq_pnum (p : Fin b.n) :
    b.numB S M p = S.pnum M (b.vtx p) (S.st (b.lt p)) (.inf (b.rightW p)) (.inf (b.leftW p)) :=
  rfl

/-- One step backward closure of `PR`. -/
theorem PR_of_rel {p : Fin b.n} {x y : M} (hxy : MonomialData.Rel (b.lt p) x y)
    (hy : y ∈ b.PR S M (b.succ p)) : x ∈ b.PR S M p := by
  rw [PR, b.plus_rightW S hA M p, MonomialData.mem_tr_iff]
  exact ⟨y, hxy, hy⟩

/-- One step forward closure of `PL`. -/
theorem PL_of_rel {p : Fin b.n} {x y : M} (hxy : MonomialData.Rel (b.lt p) x y)
    (hx : x ∈ b.PL S M p) : y ∈ b.PL S M (b.succ p) := by
  rw [PL, b.plus_leftW S hA M p, MonomialData.mem_tr_iff]
  exact ⟨x, (MonomialData.rel_inv _ _ _).mpr hxy, hx⟩

theorem PR_step {p : Fin b.n} {x : M} (hx : x ∈ b.PR S M p) :
    ∃ y, MonomialData.Rel (b.lt p) x y ∧ y ∈ b.PR S M (b.succ p) := by
  rw [PR, b.plus_rightW S hA M p, MonomialData.mem_tr_iff] at hx
  exact hx

theorem PL_step {p : Fin b.n} {y : M} (hy : y ∈ b.PL S M (b.succ p)) :
    ∃ x, MonomialData.Rel (b.lt p) x y ∧ x ∈ b.PL S M p := by
  rw [PL, b.plus_leftW S hA M p, MonomialData.mem_tr_iff] at hy
  obtain ⟨x, h1, h2⟩ := hy
  exact ⟨x, (MonomialData.rel_inv _ _ _).mp h1, h2⟩

/-- A vector of the numerator has a successor in the next numerator. -/
theorem numB_succ {p : Fin b.n} {x : M} (hx : x ∈ b.numB S M p) :
    ∃ y ∈ b.numB S M (b.succ p), MonomialData.Rel (b.lt p) x y := by
  obtain ⟨y, hxy, hy⟩ := b.PR_step S hA M hx.1
  exact ⟨y, ⟨hy, b.PL_of_rel S hA M hxy hx.2⟩, hxy⟩

/-- A vector of the numerator has a predecessor in the previous numerator. -/
theorem numB_pred {p : Fin b.n} {y : M} (hy : y ∈ b.numB S M (b.succ p)) :
    ∃ x ∈ b.numB S M p, MonomialData.Rel (b.lt p) x y := by
  obtain ⟨x, hxy, hx⟩ := b.PL_step S hA M hy.2
  exact ⟨x, ⟨b.PR_of_rel S hA M hxy hy.1, hx⟩, hxy⟩

theorem PL_of_ch {p : Fin b.n} {m : ℕ} {x y : M} (h : b.Ch M p m x y) (hx : x ∈ b.PL S M p) :
    y ∈ b.PL S M (b.succ^[m] p) := by
  induction m generalizing p x with
  | zero =>
      have : x = y := h
      subst this; simpa using hx
  | succ m ih =>
      obtain ⟨z, hz, hrest⟩ := h
      rw [Function.iterate_succ_apply]
      exact ih hrest (b.PL_of_rel S hA M hz hx)

theorem PR_of_ch {p : Fin b.n} {m : ℕ} {x y : M} (h : b.Ch M p m x y)
    (hy : y ∈ b.PR S M (b.succ^[m] p)) : x ∈ b.PR S M p := by
  induction m generalizing p x with
  | zero =>
      have : x = y := h
      subst this; simpa using hy
  | succ m ih =>
      obtain ⟨z, hz, hrest⟩ := h
      rw [Function.iterate_succ_apply] at hy
      exact b.PR_of_rel S hA M hz (ih hrest hy)

theorem numB_ch {p : Fin b.n} {m : ℕ} {x : M} (hx : x ∈ b.numB S M p) :
    ∃ y ∈ b.numB S M (b.succ^[m] p), b.Ch M p m x y := by
  induction m generalizing p x with
  | zero => exact ⟨x, by simpa using hx, (ch_zero_len b M).mpr rfl⟩
  | succ m ih =>
      obtain ⟨z, hz, hxz⟩ := b.numB_succ S hA M hx
      obtain ⟨y, hy, hch⟩ := ih hz
      exact ⟨y, by rwa [Function.iterate_succ_apply], z, hxz, hch⟩

theorem numB_ch_back {p : Fin b.n} {m : ℕ} {y : M} (hy : y ∈ b.numB S M (b.succ^[m] p)) :
    ∃ x ∈ b.numB S M p, b.Ch M p m x y := by
  induction m generalizing p y with
  | zero => exact ⟨y, by simpa using hy, (ch_zero_len b M).mpr rfl⟩
  | succ m ih =>
      rw [Function.iterate_succ_apply] at hy
      obtain ⟨z, hz, hch⟩ := ih hy
      obtain ⟨x, hx, hxz⟩ := b.numB_pred S hA M hz
      exact ⟨x, hx, z, hxz, hch⟩

omit hA [FiniteDimensional k M] in
variable {b} in
/-- The band relation at `p`: chains along one period. -/
def bandRel (p : Fin b.n) : Submodule k (M × M) where
  carrier := {xy | b.Ch M p b.n xy.1 xy.2}
  add_mem' := fun h h' ↦ b.ch_add M h h'
  zero_mem' := b.ch_zero M p b.n
  smul_mem' := fun c _ h ↦ b.ch_smul M c h

omit hA [FiniteDimensional k M] in
theorem mem_bandRel {p : Fin b.n} {x y : M} : (x, y) ∈ bandRel M p ↔ b.Ch M p b.n x y :=
  Iff.rfl

theorem bandRel_dom (p : Fin b.n) :
    ∀ x ∈ b.numB S M p, ∃ y ∈ b.numB S M p, (x, y) ∈ bandRel M p := by
  intro x hx
  obtain ⟨y, hy, hch⟩ := b.numB_ch S hA M (m := b.n) hx
  rw [b.iter_succ_n] at hy
  exact ⟨y, hy, hch⟩

theorem bandRel_ran (p : Fin b.n) :
    ∀ y ∈ b.numB S M p, ∃ x ∈ b.numB S M p, (x, y) ∈ bandRel M p := by
  intro y hy
  rw [← b.iter_succ_n p] at hy
  obtain ⟨x, hx, hch⟩ := b.numB_ch_back S hA M hy
  exact ⟨x, hx, hch⟩

omit [FiniteDimensional k M] in
theorem PR_of_minus {p : Fin b.n} {x : M} {m : ℕ} (h : b.Ch M p m x 0) : x ∈ b.PR S M p :=
  S.minus_le_plus (b.valid_rightW S hA p) ((b.mem_minus_right S M).mpr ⟨m, h⟩)

omit hA [FiniteDimensional k M] in
/-- Vectors of `K_j` have chains of `j` periods to `0`. -/
theorem ch_of_Kd {p : Fin b.n} {j : ℕ} {x : M}
    (hx : x ∈ Split.Kd (bandRel M p) (b.numB S M p) j) : b.Ch M p (j * b.n) x 0 := by
  induction j generalizing x with
  | zero => rw [Nat.zero_mul]; exact (ch_zero_len b M).mpr ((Submodule.mem_bot k).mp hx)
  | succ j ih =>
      obtain ⟨-, y, hy, hR⟩ := (Split.mem_Kd_succ _ _).mp hx
      rw [show (j + 1) * b.n = b.n + j * b.n by ring]
      exact b.ch_append M hR (by rw [b.iter_succ_n]; exact ih hy)

/-- Vectors of the numerator with chains of `j` periods to `0` lie in `K_j`. -/
theorem Kd_of_ch {p : Fin b.n} {j : ℕ} {x : M} (hxN : x ∈ b.numB S M p)
    (h : b.Ch M p (j * b.n) x 0) : x ∈ Split.Kd (bandRel M p) (b.numB S M p) j := by
  induction j generalizing x with
  | zero => exact (Submodule.mem_bot k).mpr ((ch_zero_len b M).mp (by simpa using h))
  | succ j ih =>
      rw [show (j + 1) * b.n = b.n + j * b.n by ring] at h
      obtain ⟨y, h1, h2⟩ := b.ch_split M h
      rw [b.iter_succ_n] at h2
      have hyL : y ∈ b.PL S M p := by
        have := b.PL_of_ch S hA M h1 hxN.2
        rwa [b.iter_succ_n] at this
      have hyN : y ∈ b.numB S M p := ⟨b.PR_of_minus S hA M h2, hyL⟩
      exact (Split.mem_Kd_succ _ _).mpr ⟨hxN, y, ih hyN h2, h1⟩

/-- Vectors of the numerator reached from `0` by chains of whole periods lie in `K`. -/
theorem Kinf_of_ch_zero {p : Fin b.n} {j : ℕ} {x : M} (hxN : x ∈ b.numB S M p)
    (h : b.Ch M p (j * b.n) 0 x) : x ∈ Split.Kinf (bandRel M p) (b.numB S M p) := by
  induction j generalizing x with
  | zero =>
      have : (0 : M) = x := (ch_zero_len b M).mp (by simpa using h)
      rw [← this]; exact Submodule.zero_mem _
  | succ j ih =>
      rw [Nat.succ_mul] at h
      obtain ⟨y, h1, h2⟩ := b.ch_split M h
      rw [b.iter_succ_mul] at h2
      have hyL : y ∈ b.PL S M p := by
        have := b.PL_of_ch S hA M h1 (Submodule.zero_mem _)
        rwa [b.iter_succ_mul] at this
      have hyR : y ∈ b.PR S M p := by
        refine b.PR_of_ch S hA M h2 ?_
        rw [b.iter_succ_n]; exact hxN.1
      exact Split.fwd_mem (b.bandRel_dom S hA M p) (b.bandRel_ran S hA M p)
        (ih ⟨hyR, hyL⟩ h1) hxN h2

/-- The denominator at a band position is the part of the numerator with chains to `0`. -/
theorem denB_eq (p : Fin b.n) :
    b.denB S M p = Split.Kinf (bandRel M p) (b.numB S M p) := by
  apply le_antisymm
  · refine sup_le (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · obtain ⟨hxm, hxL⟩ := Submodule.mem_inf.mp hx
      obtain ⟨m, hm⟩ := (b.mem_minus_right S M).mp hxm
      have hxN : x ∈ b.numB S M p := ⟨b.PR_of_minus S hA M hm, hxL⟩
      refine Split.Kd_le_Kinf _ _ m (b.Kd_of_ch S hA M hxN (b.ch_pad M hm ?_))
      exact Nat.le_mul_of_pos_right m b.n_pos
    · obtain ⟨hxR, hxm⟩ := Submodule.mem_inf.mp hx
      obtain ⟨m, hm⟩ := (b.mem_minus_left S M).mp hxm
      have hxL : x ∈ b.PL S M p := S.minus_le_plus (b.valid_leftW S hA p) hxm
      have hle : m ≤ m * b.n := Nat.le_mul_of_pos_right m b.n_pos
      have h := b.ch_pad_left M (r := m * b.n - m) hm
      rw [Nat.sub_add_cancel hle, b.iter_pred_mul] at h
      exact b.Kinf_of_ch_zero S hA M ⟨hxR, hxL⟩ h
  · intro x hx
    obtain ⟨j, hj⟩ := (Split.mem_Kinf_iff _ _).mp hx
    have hxN := Split.Kd_le_N _ _ j hj
    refine Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨?_, hxN.2⟩)
    exact (b.mem_minus_right S M).mpr ⟨_, b.ch_of_Kd S M hj⟩

/-- **Splitting at a band position**: the numerator is `U ⊕ den` with `U` carried to
itself by an automorphism along one period. -/
theorem exists_band_split (p : Fin b.n) :
    ∃ (U : Submodule k M) (τ : U ≃ₗ[k] U), U ≤ b.numB S M p ∧ U ⊓ b.denB S M p = ⊥ ∧
      U ⊔ b.denB S M p = b.numB S M p ∧ ∀ u : U, b.Ch M p b.n u (τ u) := by
  rw [b.denB_eq S hA M p]
  exact Split.exists_split (b.bandRel_dom S hA M p) (b.bandRel_ran S hA M p)

end CWord

end BrickAccessibility
