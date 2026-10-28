module

public import BrickAccessibility.StringQuotient.Key

/-!
# The socle of `A e_x` at a binomial vertex

At a binomial vertex `x`, every nonzero element of `A e_x` generates the longest paths
from `x` (`socle`). Modulo multiples of longest paths at binomial vertices, the nonzero
paths from `x` are linearly independent (`coeff_eq_zero`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

namespace PathData

variable {k : Type*} [Field k] {Q : FinQuiver} {A : Type*} [Ring A] [Algebra k A]
  {D : PathData Q A}

theorem pval_mul_e_eq (y x : Q.V) (l : List Q.A) :
    D.pval y l * D.e x = if y = x then D.pval x l else 0 := by
  split_ifs with h
  · subst h; exact D.pval_mul_e y l
  · rw [← D.pval_mul_e y l, mul_assoc, D.e_mul_e_of_ne h, mul_zero]

/-- Every element of `A e_x` is a combination of nonzero paths from `x`. -/
theorem exists_rep (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    {x : Q.V} {w : A} (hw : w * D.e x = w) :
    ∃ (T : Finset (List Q.A)) (g : List Q.A → k), (∀ l ∈ T, D.pval x l ≠ 0) ∧
      w = ∑ l ∈ T, g l • D.pval x l := by
  classical
  have h1 : w ∈ Submodule.span k (Set.range (D.pval x)) := by
    have hw' : w ∈ (Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2))).map
        (LinearMap.mulRight k (D.e x)) := by
      rw [hspan]; exact ⟨w, trivial, hw⟩
    rw [Submodule.map_span] at hw'
    refine Submodule.span_le.mpr ?_ hw'
    rintro _ ⟨_, ⟨⟨y, l⟩, rfl⟩, rfl⟩
    simp only [LinearMap.mulRight_apply]
    rw [pval_mul_e_eq]
    split_ifs
    · exact Submodule.subset_span ⟨l, rfl⟩
    · exact Submodule.zero_mem _
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  refine ⟨c.support.filter (fun l ↦ D.pval x l ≠ 0), c, fun l hl ↦ (Finset.mem_filter.mp hl).2, ?_⟩
  rw [← hc, Finsupp.sum]
  exact (Finset.sum_filter_of_ne fun l _ h ↦ right_ne_zero_of_smul h).symm

theorem sum_drop_nil {x : Q.V} (T : Finset (List Q.A)) (g : List Q.A → k)
    (h0 : [] ∈ T → g [] = 0) :
    ∑ l ∈ T, g l • D.pval x l = ∑ l ∈ T.filter (· ≠ []), g l • D.pval x l := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  split_ifs with h
  · rfl
  · push Not at h
    subst h
    rw [h0 hl, zero_smul]

variable (hadm : D.IsAdmissible) (hsb : D.IsSpecialBiserial)
include hadm hsb

/-- At a binomial vertex the longest paths span the line of any one of them. -/
theorem tops_le {x : Q.V} (hb : Bin (k := k) hadm x) {a0 : Q.A} (ha0 : Q.src a0 = x) :
    Submodule.span k (Tops hadm x) ≤ Submodule.span k {D.pval x (Pm hadm a0)} := by
  obtain ⟨a, b, hab, hxa, hxb, hmem⟩ := hb
  set S := Submodule.span k {D.pval x (Pm hadm a0)}
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    exact pval_Pm_ne hadm hsb hxa hμ.symm
  have hpb : D.pval x (Pm hadm b) ∈ Submodule.span k {D.pval x (Pm hadm a)} :=
    Submodule.mem_span_singleton.mpr ⟨μ⁻¹, by rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]⟩
  have hS : D.pval x (Pm hadm a) ∈ S ∧ D.pval x (Pm hadm b) ∈ S := by
    rcases eq_or_ne a0 a with rfl | h
    · exact ⟨Submodule.mem_span_singleton_self _, hpb⟩
    · have : b = a0 := out_two hsb hxa hxb ha0 hab.symm h
      subst this
      exact ⟨hmem, Submodule.mem_span_singleton_self _⟩
  rw [Submodule.span_le]
  rintro _ ⟨c, hxc, rfl⟩
  rcases eq_or_ne c a with rfl | h
  · exact hS.1
  · have : b = c := out_two hsb hxa hxb hxc hab.symm h
    subst this
    exact hS.2

/-- A nonzero path from `x` whose coefficient is nonzero is a longest path, once no
multiplication by a path of positive length survives. -/
theorem top_of_kill {x : Q.V} (T : Finset (List Q.A)) (g : List Q.A → k)
    (hT : ∀ l ∈ T, D.pval x l ≠ 0) (h0 : [] ∈ T → g [] = 0)
    (hkill : ∀ y σ, σ ≠ [] → D.pval y σ * ∑ l ∈ T, g l • D.pval x l ∈
      Submodule.span k (Tops hadm x) → D.pval y σ * ∑ l ∈ T, g l • D.pval x l = 0)
    {l : List Q.A} (hl : l ∈ T) (hg : g l ≠ 0) : ∃ a, l = Pm hadm a ∧ Q.src a = x := by
  classical
  rcases l with _ | ⟨a, t⟩
  · exact absurd (h0 hl) hg
  have hxa := D.src_eq_of_ne (hT _ hl)
  have hle := (prefix_Pm hadm hsb (hT _ hl)).length_le
  simp only [Pm, List.length_cons] at hle
  by_cases hlt : t.length < (tl hadm a).length
  · exfalso
    obtain ⟨y, σ, hσ, hne, hmem⟩ := exists_kill hadm hsb (T.filter (· ≠ [])) g
      (fun l hl ↦ ⟨(Finset.mem_filter.mp hl).2, hT l (Finset.mem_filter.mp hl).1⟩)
      (Finset.mem_filter.mpr ⟨hl, List.cons_ne_nil a t⟩) hg hlt
    rw [← sum_drop_nil T g h0] at hne hmem
    exact hne (hkill y σ hσ hmem)
  · exact ⟨a, (prefix_Pm hadm hsb (hT _ hl)).eq_of_length (by simp only [Pm, List.length_cons]; omega),
      hxa⟩

/-- **The socle of `A e_x`** at a binomial vertex: every nonzero element generates a longest
path. -/
theorem socle (hspan : Submodule.span k (Set.range (fun p : Q.V × List Q.A ↦ D.pval p.1 p.2)) = ⊤)
    {x : Q.V} (hb : Bin (k := k) hadm x) {a0 : Q.A} (ha0 : Q.src a0 = x) {w : A}
    (hw : w * D.e x = w) (hw0 : w ≠ 0) : ∃ c : A, c * w = D.pval x (Pm hadm a0) := by
  classical
  obtain ⟨T, g, hT, rfl⟩ := exists_rep hspan hw
  set p0 := D.pval x (Pm hadm a0)
  have fin : ∀ v, v ∈ Submodule.span k {p0} → v ≠ 0 → ∃ c : A, c * v = p0 := by
    intro v hv hv0
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hμ : μ ≠ 0 := by rintro rfl; simp at hv0
    exact ⟨algebraMap k A μ⁻¹, by rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hμ, one_smul]⟩
  by_cases he : [] ∈ T ∧ g [] ≠ 0
  · obtain ⟨hmem, hg⟩ := he
    set r := ∑ l ∈ T.erase [], g l • D.pval x l
    have hr : r ∈ D.RadGe k 1 := Submodule.sum_mem _ fun l hl ↦
      Submodule.smul_mem _ _ (pval_mem_rad x (Finset.ne_of_mem_erase hl))
    have hre : r * D.e x = r := by
      simp only [r, Finset.sum_mul, smul_mul_assoc, D.pval_mul_e]
    have hw' : ∑ l ∈ T, g l • D.pval x l = (algebraMap k A (g []) + r) * D.e x := by
      rw [← Finset.add_sum_erase T _ hmem, add_mul, hre, ← Algebra.smul_def]
      rfl
    obtain ⟨u, hu⟩ := isUnit_add hadm hg hr
    refine ⟨p0 * ↑u⁻¹, ?_⟩
    rw [hw', ← hu, mul_assoc, ← mul_assoc (↑u⁻¹ : A), Units.inv_mul, one_mul]
    exact D.pval_mul_e x _
  · have h0 : [] ∈ T → g [] = 0 := fun h ↦ by by_contra h'; exact he ⟨h, h'⟩
    by_cases hall : ∀ l ∈ T, g l ≠ 0 → ∃ a, l = Pm hadm a ∧ Q.src a = x
    · apply fin _ _ hw0
      refine tops_le hadm hsb hb ha0 (Submodule.sum_mem _ fun l hl ↦ ?_)
      by_cases hg : g l = 0
      · rw [hg, zero_smul]; exact Submodule.zero_mem _
      · obtain ⟨a, rfl, hxa⟩ := hall l hl hg
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hxa, rfl⟩)
    · push Not at hall
      obtain ⟨l, hl, hg, hnt⟩ := hall
      by_contra hno
      obtain ⟨a, h1, h2⟩ := top_of_kill hadm hsb T g hT h0 (fun y σ _ hmem ↦ by
        by_contra hne
        obtain ⟨c, hc⟩ := fin _ (tops_le hadm hsb hb ha0 hmem) hne
        exact hno ⟨c * D.pval y σ, by rw [mul_assoc, hc]⟩) hl hg
      exact hnt a h1 h2

/-- **Coefficients vanish modulo the socle.** -/
theorem coeff_eq_zero {x : Q.V} (T : Finset (List Q.A)) (g : List Q.A → k)
    (hT : ∀ l ∈ T, D.pval x l ≠ 0 ∧ (Bin (k := k) hadm x → ∀ a, l ≠ Pm hadm a))
    (hkill : ∀ y σ, σ ≠ [] → D.pval y σ * ∑ l ∈ T, g l • D.pval x l = 0)
    (hrad : ∑ l ∈ T, g l • D.pval x l ∈ D.RadGe k 1)
    (hnb : ¬ Bin (k := k) hadm x → ∑ l ∈ T, g l • D.pval x l = 0) :
    ∀ l ∈ T, g l = 0 := by
  classical
  have h0 : [] ∈ T → g [] = 0 := by
    intro hmem
    by_contra hg
    have hr : ∑ l ∈ T.erase [], g l • D.pval x l ∈ D.RadGe k 1 := Submodule.sum_mem _ fun l hl ↦
      Submodule.smul_mem _ _ (pval_mem_rad x (Finset.ne_of_mem_erase hl))
    rw [← Finset.add_sum_erase T _ hmem] at hrad
    have h1 := Submodule.sub_mem _ hrad hr
    rw [add_sub_cancel_right] at h1
    have h2 := Submodule.smul_mem _ (g [])⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ hg, one_smul] at h2
    exact e_not_mem hadm x h2
  have htop : ∀ l ∈ T, g l ≠ 0 → ∃ a, l = Pm hadm a ∧ Q.src a = x := fun l hl hg ↦
    top_of_kill hadm hsb T g (fun l hl ↦ (hT l hl).1) h0 (fun y σ hσ _ ↦ hkill y σ hσ) hl hg
  intro l hl
  by_contra hg
  obtain ⟨a, rfl, hxa⟩ := htop _ hl hg
  have hnb' : ¬ Bin (k := k) hadm x := fun hb ↦ (hT _ hl).2 hb a rfl
  have hw := hnb hnb'
  rw [← Finset.add_sum_erase T _ hl] at hw
  by_cases hex : ∃ l' ∈ T.erase (Pm hadm a), g l' ≠ 0
  · obtain ⟨l', hl', hg'⟩ := hex
    obtain ⟨b, rfl, hxb⟩ := htop _ (Finset.mem_of_mem_erase hl') hg'
    have hba : b ≠ a := by rintro rfl; exact Finset.ne_of_mem_erase hl' rfl
    rw [Finset.sum_eq_single_of_mem (Pm hadm b) hl' (fun l'' hl'' hne ↦ by
      by_contra h
      have hg'' : g l'' ≠ 0 := fun h' ↦ h (by rw [h', zero_smul])
      obtain ⟨c, rfl, hxc⟩ := htop _ (Finset.mem_of_mem_erase hl'') hg''
      have hca : c ≠ a := by rintro rfl; exact Finset.ne_of_mem_erase hl'' rfl
      exact hne (by rw [out_two hsb hxa hxc hxb hca hba])) ] at hw
    apply hnb'
    refine ⟨a, b, hba.symm, hxa, hxb, Submodule.mem_span_singleton.mpr
      ⟨-(g (Pm hadm a))⁻¹ * g (Pm hadm b), ?_⟩⟩
    have h1 : g (Pm hadm a) • D.pval x (Pm hadm a) = -(g (Pm hadm b) • D.pval x (Pm hadm b)) :=
      eq_neg_of_add_eq_zero_left hw
    rw [mul_smul, neg_smul, ← smul_neg, ← h1, smul_smul, inv_mul_cancel₀ hg, one_smul]
  · push Not at hex
    rw [Finset.sum_eq_zero (fun l' hl' ↦ by rw [hex l' hl', zero_smul]), add_zero] at hw
    exact smul_ne_zero hg (pval_Pm_ne hadm hsb hxa) hw

end PathData

end BrickAccessibility
