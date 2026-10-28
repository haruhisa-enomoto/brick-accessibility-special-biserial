module

public import BrickAccessibility.Section4.EndpointFacts

/-!
# Lemma 4.6: the endpoint deficit

For a string `w` of positive length over a representation-finite gentle algebra,
in which no vertex carries both a top position and a socle position (true for
nonsimple bricks by (2.1)), some vertex `v` satisfies `extout_v < socend_v` or
`extin_v < topend_v`. Otherwise the extending arrows at the two endpoints close
`w` up into a closed word with all cyclic pairs allowed, which is impossible
in finite representation type (`not_isRepFinite_of_closed`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace BrickAccessibility

open BrickAccessibility.Statement

universe u

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

namespace Word

variable {D : MonomialData k B} (w : Word D.Q) (hSB : D.toPathData.IsSpecialBiserial)
  (hs : w.IsString D) (hn : 0 < w.len)
include hSB hs hn

/-- In the both-socle case, outgoing extending arrows exist at both endpoints with
targets `x, y` or `y, x`. -/
theorem extract_socle_pair (H : ∀ v, w.socend v ≤ w.extout v)
    (h0 : ∃ a i, w.next a i = some 0) (hl : ∃ a i, w.next a i = some (Fin.last _)) :
    ∃ ρ σ, w.OutExt 0 ρ ∧ w.OutExt (Fin.last _) σ ∧
      ((D.Q.tgt ρ = w.vtx 0 ∧ D.Q.tgt σ = w.vtx (Fin.last _)) ∨
        (D.Q.tgt ρ = w.vtx (Fin.last _) ∧ D.Q.tgt σ = w.vtx 0 ∧
          w.vtx 0 ≠ w.vtx (Fin.last _))) := by
  have hz := w.zero_ne_last hs.1 hn
  by_cases hxy : w.vtx 0 = w.vtx (Fin.last _)
  · have h2 := (w.socend_two hs.1 hn hxy h0 hl).trans (H _)
    obtain ⟨p, c, p', c', hp, hc, htc, hp', hc', htc', hne⟩ := w.extract_out_two h2
    rw [w.isEnd_iff] at hp hp'
    rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
    · exact absurd (by rw [w.outExt_zero_unique hn hSB hc hc']) hne
    · exact ⟨c, c', hc, hc', Or.inl ⟨htc, htc'.trans hxy⟩⟩
    · exact ⟨c', c, hc', hc, Or.inl ⟨htc', htc.trans hxy⟩⟩
    · exact absurd (by rw [w.outExt_last_unique hn hSB hc hc']) hne
  · obtain ⟨p, c, hp, hc, htc⟩ := w.extract_out ((w.socend_pos hs.1 hn (Or.inl rfl) h0).trans (H _))
    obtain ⟨p', c', hp', hc', htc'⟩ :=
      w.extract_out ((w.socend_pos hs.1 hn (Or.inr rfl) hl).trans (H _))
    rw [w.isEnd_iff] at hp hp'
    rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
    · exact absurd (htc.symm.trans ((w.outExt_zero_unique hn hSB hc hc') ▸ htc')) hxy
    · exact ⟨c, c', hc, hc', Or.inl ⟨htc, htc'⟩⟩
    · exact ⟨c', c, hc', hc, Or.inr ⟨htc', htc, hxy⟩⟩
    · exact absurd (htc.symm.trans ((w.outExt_last_unique hn hSB hc hc') ▸ htc')) hxy

/-- In the both-top case, incoming extending arrows exist at both endpoints with
sources `x, y` or `y, x`. -/
theorem extract_top_pair (H : ∀ v, w.topend v ≤ w.extin v)
    (h0 : ∃ a j, w.next a 0 = some j) (hl : ∃ a j, w.next a (Fin.last _) = some j) :
    ∃ ρ σ, w.InExt 0 ρ ∧ w.InExt (Fin.last _) σ ∧
      ((D.Q.src ρ = w.vtx 0 ∧ D.Q.src σ = w.vtx (Fin.last _)) ∨
        (D.Q.src ρ = w.vtx (Fin.last _) ∧ D.Q.src σ = w.vtx 0 ∧
          w.vtx 0 ≠ w.vtx (Fin.last _))) := by
  have hz := w.zero_ne_last hs.1 hn
  by_cases hxy : w.vtx 0 = w.vtx (Fin.last _)
  · have h2 := (w.topend_two hs.1 hn hxy h0 hl).trans (H _)
    obtain ⟨p, c, p', c', hp, hc, htc, hp', hc', htc', hne⟩ := w.extract_in_two h2
    rw [w.isEnd_iff] at hp hp'
    rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
    · exact absurd (by rw [w.inExt_zero_unique hn hSB hc hc']) hne
    · exact ⟨c, c', hc, hc', Or.inl ⟨htc, htc'.trans hxy⟩⟩
    · exact ⟨c', c, hc', hc, Or.inl ⟨htc', htc.trans hxy⟩⟩
    · exact absurd (by rw [w.inExt_last_unique hn hSB hc hc']) hne
  · obtain ⟨p, c, hp, hc, htc⟩ := w.extract_in ((w.topend_pos hs.1 hn (Or.inl rfl) h0).trans (H _))
    obtain ⟨p', c', hp', hc', htc'⟩ :=
      w.extract_in ((w.topend_pos hs.1 hn (Or.inr rfl) hl).trans (H _))
    rw [w.isEnd_iff] at hp hp'
    rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
    · exact absurd (htc.symm.trans ((w.inExt_zero_unique hn hSB hc hc') ▸ htc')) hxy
    · exact ⟨c, c', hc, hc', Or.inl ⟨htc, htc'⟩⟩
    · exact ⟨c', c, hc', hc, Or.inr ⟨htc', htc, hxy⟩⟩
    · exact absurd (htc.symm.trans ((w.inExt_last_unique hn hSB hc hc') ▸ htc')) hxy

end Word

section Cases

variable [IsAlgClosed k] [FiniteDimensional k B] {D : MonomialData k B} (hD : D.IsGentle)
  (hrep : IsRepFinite B) (w : Word D.Q) (hs : w.IsString D) (hn : 0 < w.len)
include hD hrep hs hn

/-- Both endpoints are socle endpoints. -/
theorem case_socle_socle (H : ∀ v, w.socend v ≤ w.extout v) (a0 az : D.Q.A)
    (hf : w.first hn = (a0, false)) (hz : w.last hn = (az, true)) : False := by
  have hSB := hD.1.2
  have h0 : ∃ a i, w.next a i = some 0 := (w.in_zero_iff hs.1 hn).mpr (by rw [hf])
  have hl : ∃ a i, w.next a i = some (Fin.last _) := (w.in_last_iff hs.1 hn).mpr (by rw [hz])
  have hfs := w.first_src hn; rw [hf] at hfs; simp only [Letter.src] at hfs
  have hzt := w.last_tgt hn; rw [hz] at hzt; simp only [Letter.tgt, if_true] at hzt
  obtain ⟨ρ, σ, hρ, hσ, hcase⟩ := w.extract_socle_pair hSB hs hn H h0 hl
  rw [w.outExt_zero_iff hn, hf] at hρ
  rw [w.outExt_last_iff hn, hz] at hσ
  simp only [Bool.false_eq_true, if_false, if_true] at hρ hσ
  rcases hcase with ⟨hρt, hσt⟩ | ⟨hρt, hσt, hxy⟩
  · -- loops at both endpoints: the closed word `w σ w⁻¹ ρ`
    have hρa : ρ ≠ a0 := by
      rintro rfl
      exact hρ.2 (D.pval_loop_eq_zero hD (hρ.1.trans hρt.symm))
    have hσa : σ ≠ az := by
      rintro rfl
      exact hσ.2 (D.pval_loop_eq_zero hD (hσ.1.trans hσt.symm))
    refine w.shape_two hn hD hs (σ, true) (ρ, true) (by simpa [Letter.src] using hσ.1)
      (by simpa [Letter.tgt] using hσt) (by simpa [Letter.src] using hρ.1)
      (by simpa [Letter.tgt] using hρt) ?_ ?_ ?_ ?_ hrep
    · rw [hz]; simpa using hσ.2
    · rw [hz]; simpa [Letter.inv] using hσa
    · rw [hf]; simpa [Letter.inv] using hρ.2
    · rw [hf]; simpa using hρa
  · -- arrows `ρ : x → y` and `σ : y → x`
    by_cases hσa : σ ≠ a0
    · refine w.shape_one hn hD hs (σ, true) (by simpa [Letter.src] using hσ.1)
        (by simpa [Letter.tgt] using hσt) ?_ ?_ hrep
      · rw [hz]; simpa using hσ.2
      · rw [hf]; simpa using hσa
    · by_cases hρa : ρ ≠ az
      · refine w.shape_three hn hD hs (ρ, true) (by simpa [Letter.src] using hρ.1)
          (by simpa [Letter.tgt] using hρt) ?_ ?_ hrep
        · rw [hf]; simpa [Letter.inv] using hρ.2
        · rw [hz]; simpa [Letter.inv] using hρa
      · push Not at hσa hρa
        subst hσa; subst hρa
        exact D.false_of_two_cycle hD (hfs.trans hρ.1.symm) (hzt.trans hσ.1.symm) hρ.2 hσ.2

/-- Both endpoints are top endpoints. -/
theorem case_top_top (H : ∀ v, w.topend v ≤ w.extin v) (a0 az : D.Q.A)
    (hf : w.first hn = (a0, true)) (hz : w.last hn = (az, false)) : False := by
  have hSB := hD.1.2
  have h0 : ∃ a j, w.next a 0 = some j := (w.out_zero_iff hs.1 hn).mpr (by rw [hf])
  have hl : ∃ a j, w.next a (Fin.last _) = some j := (w.out_last_iff hs.1 hn).mpr (by rw [hz])
  have hfs := w.first_src hn; rw [hf] at hfs; simp only [Letter.src, if_true] at hfs
  have hzt := w.last_tgt hn; rw [hz] at hzt; simp only [Letter.tgt] at hzt
  obtain ⟨ρ, σ, hρ, hσ, hcase⟩ := w.extract_top_pair hSB hs hn H h0 hl
  rw [w.inExt_zero_iff hn, hf] at hρ
  rw [w.inExt_last_iff hn, hz] at hσ
  simp only [Bool.false_eq_true, if_false, if_true] at hρ hσ
  rcases hcase with ⟨hρs, hσs⟩ | ⟨hρs, hσs, hxy⟩
  · -- loops: the closed word `w σ⁻¹ w⁻¹ ρ⁻¹`
    have hρa : ρ ≠ a0 := by
      rintro rfl
      exact hρ.2 (D.pval_loop_eq_zero hD (hρs.trans hρ.1.symm))
    have hσa : σ ≠ az := by
      rintro rfl
      exact hσ.2 (D.pval_loop_eq_zero hD (hσs.trans hσ.1.symm))
    refine w.shape_two hn hD hs (σ, false) (ρ, false) (by simpa [Letter.src] using hσ.1)
      (by simpa [Letter.tgt] using hσs) (by simpa [Letter.src] using hρ.1)
      (by simpa [Letter.tgt] using hρs) ?_ ?_ ?_ ?_ hrep
    · rw [hz]; simpa using hσ.2
    · rw [hz]; simpa [Letter.inv] using hσa
    · rw [hf]; simpa [Letter.inv] using hρ.2
    · rw [hf]; simpa using hρa
  · -- arrows `ρ : y → x` and `σ : x → y`
    by_cases hσa : σ ≠ a0
    · refine w.shape_one hn hD hs (σ, false) (by simpa [Letter.src] using hσ.1)
        (by simpa [Letter.tgt] using hσs) ?_ ?_ hrep
      · rw [hz]; simpa using hσ.2
      · rw [hf]; simpa using hσa
    · by_cases hρa : ρ ≠ az
      · refine w.shape_three hn hD hs (ρ, false) (by simpa [Letter.src] using hρ.1)
          (by simpa [Letter.tgt] using hρs) ?_ ?_ hrep
        · rw [hf]; simpa [Letter.inv] using hρ.2
        · rw [hz]; simpa [Letter.inv] using hρa
      · push Not at hσa hρa
        subst hσa; subst hρa
        exact D.false_of_two_cycle hD (hσ.1.trans hzt.symm) (hρ.1.trans hfs.symm) hσ.2 hρ.2

/-- The left endpoint is a top endpoint and the right endpoint a socle endpoint. -/
theorem case_top_socle (H : ∀ v, w.socend v ≤ w.extout v ∧ w.topend v ≤ w.extin v)
    (hxy : w.vtx 0 ≠ w.vtx (Fin.last _)) (a0 az : D.Q.A)
    (hf : w.first hn = (a0, true)) (hz : w.last hn = (az, true)) : False := by
  have hSB := hD.1.2
  have h0 : ∃ a j, w.next a 0 = some j := (w.out_zero_iff hs.1 hn).mpr (by rw [hf])
  have hl : ∃ a i, w.next a i = some (Fin.last _) := (w.in_last_iff hs.1 hn).mpr (by rw [hz])
  have hfs := w.first_src hn; rw [hf] at hfs; simp only [Letter.src, if_true] at hfs
  have hzt := w.last_tgt hn; rw [hz] at hzt; simp only [Letter.tgt, if_true] at hzt
  obtain ⟨p, ρ, hp, hρ, hρs⟩ :=
    w.extract_in ((w.topend_pos hs.1 hn (Or.inl rfl) h0).trans (H _).2)
  obtain ⟨p', σ, hp', hσ, hσt⟩ :=
    w.extract_out ((w.socend_pos hs.1 hn (Or.inr rfl) hl).trans (H _).1)
  rw [w.isEnd_iff] at hp hp'
  rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
  · -- (iii) `ρ` a loop at `x`, `σ : x → y`: three arrows out of `x`
    rw [w.inExt_zero_iff hn, hf] at hρ
    rw [w.outExt_zero_iff hn, hf] at hσ
    simp only [if_true] at hρ hσ
    have hρa : ρ ≠ a0 := by
      rintro rfl; exact hρ.2 (D.pval_loop_eq_zero hD (hρs.trans hρ.1.symm))
    have hρσ : ρ ≠ σ := by
      rintro rfl; exact hxy (hρ.1.symm.trans hσt)
    exact Word.false_of_card_le_two (hSB.1 (w.vtx 0)) (x := a0) (y := ρ) (z := σ) hfs hρs hσ.1
      (Ne.symm hρa) (Ne.symm hσ.2) hρσ
  · -- (i) loops at both ends: the closed word `w σ w⁻¹ ρ`
    rw [w.inExt_zero_iff hn, hf] at hρ
    rw [w.outExt_last_iff hn, hz] at hσ
    simp only [if_true] at hρ hσ
    have hρa : ρ ≠ a0 := by
      rintro rfl; exact hρ.2 (D.pval_loop_eq_zero hD (hρs.trans hρ.1.symm))
    have hσa : σ ≠ az := by
      rintro rfl; exact hσ.2 (D.pval_loop_eq_zero hD (hσ.1.trans hσt.symm))
    refine w.shape_two hn hD hs (σ, true) (ρ, true) (by simpa [Letter.src] using hσ.1)
      (by simpa [Letter.tgt] using hσt) (by simpa [Letter.src] using hρs)
      (by simpa [Letter.tgt] using hρ.1) ?_ ?_ ?_ ?_ hrep
    · rw [hz]; simpa using hσ.2
    · rw [hz]; simpa [Letter.inv] using hσa
    · rw [hf]; simpa [Letter.inv] using (Ne.symm hρa)
    · rw [hf]; simpa using hρ.2
  · -- (ii) `ρ, σ : x → y`
    rw [w.inExt_last_iff hn, hz] at hρ
    rw [w.outExt_zero_iff hn, hf] at hσ
    simp only [if_true] at hρ hσ
    by_cases hρσ : ρ = σ
    · subst hρσ
      refine w.shape_one hn hD hs (ρ, false) (by simpa [Letter.src] using hρ.1)
        (by simpa [Letter.tgt] using hρs) ?_ ?_ hrep
      · rw [hz]; simpa using (Ne.symm hρ.2)
      · rw [hf]; simpa using hσ.2
    · exact MonomialData.shape_four hD (ρ, true) (σ, false)
        (by simp [Letter.tgt, Letter.src, hρ.1, hσt])
        (by simp [Letter.tgt, Letter.src, hσ.1, hρs])
        (by simpa using hρσ) (by simpa using Ne.symm hρσ) hrep
  · -- (iv) `ρ : x → y`, `σ` a loop at `y`: three arrows into `y`
    rw [w.inExt_last_iff hn, hz] at hρ
    rw [w.outExt_last_iff hn, hz] at hσ
    simp only [if_true] at hρ hσ
    have hσa : σ ≠ az := by
      rintro rfl; exact hσ.2 (D.pval_loop_eq_zero hD (hσ.1.trans hσt.symm))
    have hρσ : ρ ≠ σ := by
      rintro rfl; exact hxy (hρs.symm.trans hσ.1)
    exact Word.false_of_card_le_two (hSB.2.1 (w.vtx (Fin.last _))) (x := az) (y := ρ) (z := σ)
      hzt hρ.1 hσt (Ne.symm hρ.2) (Ne.symm hσa) hρσ

/-- The left endpoint is a socle endpoint and the right endpoint a top endpoint. -/
theorem case_socle_top (H : ∀ v, w.socend v ≤ w.extout v ∧ w.topend v ≤ w.extin v)
    (hxy : w.vtx 0 ≠ w.vtx (Fin.last _)) (a0 az : D.Q.A)
    (hf : w.first hn = (a0, false)) (hz : w.last hn = (az, false)) : False := by
  have hSB := hD.1.2
  have h0 : ∃ a i, w.next a i = some 0 := (w.in_zero_iff hs.1 hn).mpr (by rw [hf])
  have hl : ∃ a j, w.next a (Fin.last _) = some j := (w.out_last_iff hs.1 hn).mpr (by rw [hz])
  have hfs := w.first_src hn; rw [hf] at hfs; simp only [Letter.src] at hfs
  have hzt := w.last_tgt hn; rw [hz] at hzt; simp only [Letter.tgt] at hzt
  obtain ⟨p, ρ, hp, hρ, hρs⟩ :=
    w.extract_in ((w.topend_pos hs.1 hn (Or.inr rfl) hl).trans (H _).2)
  obtain ⟨p', σ, hp', hσ, hσt⟩ :=
    w.extract_out ((w.socend_pos hs.1 hn (Or.inl rfl) h0).trans (H _).1)
  rw [w.isEnd_iff] at hp hp'
  rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
  · -- (iv') `ρ : y → x`, `σ` a loop at `x`: three arrows into `x`
    rw [w.inExt_zero_iff hn, hf] at hρ
    rw [w.outExt_zero_iff hn, hf] at hσ
    simp only [Bool.false_eq_true, if_false] at hρ hσ
    have hσa : σ ≠ a0 := by
      rintro rfl; exact hσ.2 (D.pval_loop_eq_zero hD (hσ.1.trans hσt.symm))
    have hρσ : ρ ≠ σ := by
      rintro rfl; exact hxy (hσ.1.symm.trans hρs)
    exact Word.false_of_card_le_two (hSB.2.1 (w.vtx 0)) (x := a0) (y := ρ) (z := σ)
      hfs hρ.1 hσt (Ne.symm hρ.2) (Ne.symm hσa) hρσ
  · -- (ii') `ρ, σ : y → x`
    rw [w.inExt_zero_iff hn, hf] at hρ
    rw [w.outExt_last_iff hn, hz] at hσ
    simp only [Bool.false_eq_true, if_false] at hρ hσ
    by_cases hρσ : ρ = σ
    · subst hρσ
      refine w.shape_one hn hD hs (ρ, true) (by simpa [Letter.src] using hσ.1)
        (by simpa [Letter.tgt] using hρ.1) ?_ ?_ hrep
      · rw [hz]; simpa using (Ne.symm hσ.2)
      · rw [hf]; simpa using hρ.2
    · exact MonomialData.shape_four hD (ρ, true) (σ, false)
        (by simp [Letter.tgt, Letter.src, hρ.1, hσt])
        (by simp [Letter.tgt, Letter.src, hσ.1, hρs])
        (by simpa using hρσ) (by simpa using Ne.symm hρσ) hrep
  · -- (i') loops at both ends: the closed word `w⁻¹ σ w ρ`
    rw [w.inExt_last_iff hn, hz] at hρ
    rw [w.outExt_zero_iff hn, hf] at hσ
    simp only [Bool.false_eq_true, if_false] at hρ hσ
    have hσa : σ ≠ a0 := by
      rintro rfl; exact hσ.2 (D.pval_loop_eq_zero hD (hσ.1.trans hσt.symm))
    have hρa : ρ ≠ az := by
      rintro rfl; exact hρ.2 (D.pval_loop_eq_zero hD (hρs.trans hρ.1.symm))
    refine w.shape_five hn hD hs (σ, true) (ρ, true) (by simpa [Letter.src] using hσ.1)
      (by simpa [Letter.tgt] using hσt) (by simpa [Letter.src] using hρs)
      (by simpa [Letter.tgt] using hρ.1) ?_ ?_ ?_ ?_ hrep
    · rw [hf]; simpa [Letter.inv] using hσ.2
    · rw [hf]; simpa using hσa
    · rw [hz]; simpa using (Ne.symm hρa)
    · rw [hz]; simpa [Letter.inv] using hρ.2
  · -- (iii') `ρ` a loop at `y`, `σ : y → x`: three arrows out of `y`
    rw [w.inExt_last_iff hn, hz] at hρ
    rw [w.outExt_last_iff hn, hz] at hσ
    simp only [Bool.false_eq_true, if_false] at hρ hσ
    have hρa : ρ ≠ az := by
      rintro rfl; exact hρ.2 (D.pval_loop_eq_zero hD (hρs.trans hρ.1.symm))
    have hρσ : ρ ≠ σ := by
      rintro rfl; exact hxy (hσt.symm.trans hρ.1)
    exact Word.false_of_card_le_two (hSB.1 (w.vtx (Fin.last _))) (x := az) (y := ρ) (z := σ)
      hzt hρs hσ.1 (Ne.symm hρa) (Ne.symm hσ.2) hρσ

end Cases

/-- **Lemma 4.6, combinatorial form.** -/
theorem exists_ext_deficit [IsAlgClosed k] [FiniteDimensional k B] {D : MonomialData k B}
    (hD : D.IsGentle) (hrep : IsRepFinite B) (w : Word D.Q) (hs : w.IsString D) (hn : 0 < w.len)
    (hts : ∀ p q, (∀ a i, w.next a i ≠ some p) → (∀ a, w.next a q = none) →
      w.vtx p ≠ w.vtx q) :
    ∃ v, w.extout v < w.socend v ∨ w.extin v < w.topend v := by
  by_contra hcon
  push Not at hcon
  rcases hf : w.first hn with ⟨a0, d0⟩
  rcases hz : w.last hn with ⟨az, dz⟩
  cases d0 <;> cases dz
  · -- left socle, right top
    have hno0 : ∀ a, w.next a 0 = none := by
      intro a; by_contra h
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp h
      have := (w.out_zero_iff hs.1 hn).mp ⟨a, j, hj⟩
      rw [hf] at this; cases this
    have hnil : ∀ a i, w.next a i ≠ some (Fin.last _) := by
      intro a i h
      have := (w.in_last_iff hs.1 hn).mp ⟨a, i, h⟩
      rw [hz] at this; cases this
    exact case_socle_top hD hrep w hs hn hcon (fun h ↦ hts _ _ hnil hno0 h.symm) a0 az hf hz
  · exact case_socle_socle hD hrep w hs hn (fun v ↦ (hcon v).1) a0 az hf hz
  · exact case_top_top hD hrep w hs hn (fun v ↦ (hcon v).2) a0 az hf hz
  · -- left top, right socle
    have hni0 : ∀ a i, w.next a i ≠ some 0 := by
      intro a i h
      have := (w.in_zero_iff hs.1 hn).mp ⟨a, i, h⟩
      rw [hf] at this; cases this
    have hnol : ∀ a, w.next a (Fin.last _) = none := by
      intro a; by_contra h
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp h
      have := (w.out_last_iff hs.1 hn).mp ⟨a, j, hj⟩
      rw [hz] at this; cases this
    exact case_top_socle hD hrep w hs hn hcon (hts _ _ hni0 hnol) a0 az hf hz

end BrickAccessibility
