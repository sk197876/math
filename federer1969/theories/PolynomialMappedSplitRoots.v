(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: every root of an original
    factor lies in the complete containing-field
    root list. Reuse coefficient-map evaluation,
    evaluation uniqueness and the split-root criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialUP
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws
  CommutativePolynomialEvaluationSealed PolynomialCoefficientMapUP PolynomialMappedEvaluation
  PolynomialLinearSplitUP PolynomialLinearSplitLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [mapped_split_original_factor_root]: the
    roots of either original minimal polynomial
    occur among the conjugates used in the
    primitive-element argument of 3.4.8(8), p. 330.
    Apply the existing product-root criterion rather
    than constructing a second containing field. *)
Theorem mapped_split_original_factor_root (K L T:fieldType) (B O:comNzRingType)
  (embedK:{rmorphism K->B}) (variableK:B) (source:B->nat->K)
  (hB:is_commutative_polynomial_ring embedK variableK source)
  (embedL:{rmorphism L->O}) (variableL:O) (original:O->nat->L)
  (hO:is_commutative_polynomial_ring embedL variableL original)
  (phi:{rmorphism K->L}) (M0:{rmorphism B->O})
  (hM0:is_polynomial_coefficient_map source original phi M0)
  (P H:B) n (psi:{rmorphism L->T}) (c:T) (roots:seq T)
  (hSplit:is_linear_polynomial_split embedL variableL (M0 P) n psi c roots)
  (u:T) (Eu:{rmorphism B->T}):
  is_commutative_polynomial_evaluation embedK variableK
    (GRing.RMorphism.clone K T (psi \o phi) _) u Eu ->
  commutative_divides H P ->Eu H = 0 ->u \in roots.
Proof.
move=>hEu [Q hFactor] hRoot.
pose EO:=@CommutativePolynomialEvaluation.map L O T embedL variableL original hO psi u.
have hEO:=@CommutativePolynomialEvaluation.laws L O T embedL variableL original hO psi u.
have hComposite:=@polynomial_evaluation_through_coefficient_map K B L O T
  embedK variableK source embedL variableL original hB hO phi M0 hM0 psi u EO hEO.
have hValue:=@polynomial_evaluation_unique K B T embedK variableK source hB
  (GRing.RMorphism.clone K T (psi \o phi) _) u
  (GRing.RMorphism.clone B T (EO \o M0) _) Eu hComposite hEu P.
have hZero:EO (M0 P) = 0.
  change (EO (M0 P) = Eu P) in hValue.
  by rewrite hValue hFactor rmorphM hRoot mulr0.
pose identity:{rmorphism T->T}:=GRing.RMorphism.clone T T idfun _.
have hCriterion:=@linear_polynomial_split_root_criterion L O embedL variableL (M0 P) n
  T psi c roots hSplit T identity psi u EO (fun a=>erefl (psi a)) hEO.
have [r [hR hU]]:=hCriterion.1 hZero.
change (u = r) in hU;by rewrite hU.
Qed.
