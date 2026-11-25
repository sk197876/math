(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: evaluation commutes with extension
    of the original coefficients. Apply the existing
    coefficient-map laws and polynomial evaluation
    uniqueness from 3.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP PolynomialCoefficientMapUP PolynomialCoefficientMapLaws
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [polynomial_evaluation_coefficient_extension]:
    scalar extension preserves the original polynomial
    evaluation, supporting the finite-separable argument
    of 3.4.8(8), pp. 329–330. Prove only the
    connection between the two existing interfaces. *)
Theorem polynomial_evaluation_coefficient_extension (A B C D T:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
  (hSource:is_commutative_polynomial_ring embedA variableA source)
  (hTarget:is_commutative_polynomial_ring embedC variableC target)
  (phi:{rmorphism A->C}) (M:{rmorphism B->D})
  (hM:is_polynomial_coefficient_map source target phi M)
  (chi:{rmorphism A->T}) (psi:{rmorphism C->T}) (x:T)
  (E:{rmorphism B->T}) (F:{rmorphism D->T}):
  (forall a:A,chi a = psi (phi a)) ->
  is_commutative_polynomial_evaluation embedA variableA chi x E ->
  is_commutative_polynomial_evaluation embedC variableC psi x F ->
  forall P:B,E P = F (M P).
Proof.
move=>hChi hE hF.
pose FM:{rmorphism B->T}:=GRing.RMorphism.clone B T (F \o M) _.
have hFM:is_commutative_polynomial_evaluation embedA variableA chi x FM.
  constructor.
  - move=>a;change (F (M (embedA a)) = chi a).
    rewrite (@polynomial_coefficient_map_constant A B C D embedA variableA source embedC variableC target
      hSource hTarget phi M hM) (polynomial_evaluation_constants hF).
    exact:esym (hChi a).
  - change (F (M variableA) = x).
    rewrite (@polynomial_coefficient_map_variable A B C D embedA variableA source embedC variableC target
      hSource hTarget phi M hM).
    exact:polynomial_evaluation_variable hF.
exact:(@polynomial_evaluation_unique A B T embedA variableA source hSource chi x E FM hE hFM).
Qed.
