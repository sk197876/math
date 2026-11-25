(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: evaluating an original coefficient
    extension composes its scalar map. Reuse the
    existing coefficient-map constant and variable laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  PolynomialCoefficientMapUP PolynomialCoefficientMapLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [polynomial_evaluation_through_coefficient_map]:
    the original polynomial evaluation after coefficient
    extension in the commuting field diagrams of
    3.4.8(8), pp. 329–330. Only the existing
    independent constant and variable equations are used. *)
Theorem polynomial_evaluation_through_coefficient_map (A B C D T:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
  (hSource:is_commutative_polynomial_ring embedA variableA source)
  (hTarget:is_commutative_polynomial_ring embedC variableC target)
  (phi:{rmorphism A->C}) (M:{rmorphism B->D})
  (hM:is_polynomial_coefficient_map source target phi M)
  (psi:{rmorphism C->T}) (x:T) (E:{rmorphism D->T}):
  is_commutative_polynomial_evaluation embedC variableC psi x E ->
  is_commutative_polynomial_evaluation embedA variableA
    (GRing.RMorphism.clone A T (psi \o phi) _) x
    (GRing.RMorphism.clone B T (E \o M) _).
Proof.
move=>hE;constructor.
- move=>a;change (E (M (embedA a)) = psi (phi a)).
  by rewrite (@polynomial_coefficient_map_constant A B C D embedA variableA source embedC variableC target
    hSource hTarget phi M hM) (polynomial_evaluation_constants hE).
- change (E (M variableA) = x).
  rewrite (@polynomial_coefficient_map_variable A B C D embedA variableA source embedC variableC target
    hSource hTarget phi M hM).
  exact:polynomial_evaluation_variable hE.
Qed.
