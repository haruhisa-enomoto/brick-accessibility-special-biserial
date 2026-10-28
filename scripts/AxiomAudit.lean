module

public import BrickAccessibility
public import Solution

/-! Axiom report for the main theorems and the principal statements.
Run with `lake env lean scripts/AxiomAudit.lean`, or `python3 scripts/audit_axioms.py`. -/

@[expose] public section

#print axioms BrickAccessibility.theoremA
#print axioms BrickAccessibility.corollaryB
#print axioms BrickAccessibility.corollaryBiserial
#print axioms BrickAccessibility.isSpecialBiserial_of_biserial
#print axioms BrickAccessibility.accessibility_of_smaller
#print axioms BrickAccessibility.specialBiserial_hasSmallerBrick
#print axioms BrickAccessibility.remark_5_7
#print axioms BrickAccessibility.string_or_band
#print axioms BrickAccessibility.not_isRepFinite_of_band
#print axioms BrickAccessibility.string_of_isRepFinite
#print axioms BrickAccessibility.CWord.isIndecomposable_bandModule
#print axioms BrickAccessibility.CWord.eq_of_bandModule_equiv
#print axioms BrickAccessibility.lemma_4_3_socle
#print axioms BrickAccessibility.lemma_4_3_top
#print axioms BrickAccessibility.Word.dualEquiv
#print axioms BrickAccessibility.Statement.AdmissiblePresentation.stringQuotient_exact
#print axioms BrickAccessibility.Challenge.theoremA
#print axioms BrickAccessibility.Challenge.corollaryB
#print axioms BrickAccessibility.Challenge.corollaryBiserial
