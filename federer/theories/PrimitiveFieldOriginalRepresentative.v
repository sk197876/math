(** Federer (1969), 3.4.8(8), p. 330:
    primitive ring generation gives an original
    coefficient denominator and an original
    polynomial representative for every quotient
    class. Reuse polynomial surjectivity, original
    denominator clearing and the evaluation diagrams. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP FractionFieldUP CoefficientFractionFieldUP
  CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed PolynomialCoefficientMapUP PolynomialCoefficientMapSealed
  PolynomialPrimitiveGenerator PolynomialScalarComposition PolynomialEvaluationCoefficientExtension
  CoefficientPolynomialDenominators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [primitive_field_original_coefficient_representative]:
    every original quotient class has an
    original Q_m denominator and a polynomial
    representative in the original primitive
    coordinate, 3.4.8(8), p. 330. No
    desired representative or denominator is assumed. *)
Theorem primitive_field_original_coefficient_representative (A B C:comNzRingType) (L M:fieldType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hB:is_commutative_polynomial_ring embed variable coefficient)
  (scalar:{rmorphism A->C}) (inclusion:{rmorphism C->L})
  (eta:{rmorphism A->M}) (phi:{rmorphism M->L}) (z:C) (E:{rmorphism B->C}):
  is_commutative_fraction_field inclusion ->
  is_coefficient_fraction_field (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi ->
  is_commutative_polynomial_evaluation embed variable scalar z E ->
  is_generated_commutative_subring (fun y:L=>y = inclusion z \/exists a:M,y = phi a) setT ->
  forall c:C,exists (delta:A) (P:B),eta delta<>0 /\scalar delta*c = E P.
Proof.
move=>hFraction hCoefficient hE hGenerated c.
pose BM:=CommutativePolynomial.space M.
pose embedM:=CommutativePolynomial.embed M.
pose variableM:=CommutativePolynomial.variable M.
pose coefficientM:=@CommutativePolynomial.coefficient M.
have hBM:=CommutativePolynomial.laws M.
pose F:=@CommutativePolynomialEvaluation.map M BM L embedM variableM coefficientM hBM phi (inclusion z).
have hF:=@CommutativePolynomialEvaluation.laws M BM L embedM variableM coefficientM hBM phi (inclusion z).
have hOnto:=(@polynomial_surjection_primitive_generator M BM L embedM variableM coefficientM
  hBM phi (inclusion z) F hF).2 hGenerated.
have [H hH]:=hOnto (inclusion c).
pose map:=@PolynomialCoefficientMap.map A B M BM embed variable coefficient embedM variableM coefficientM hB hBM eta.
have hMap:=@PolynomialCoefficientMap.laws A B M BM embed variable coefficient embedM variableM coefficientM hB hBM eta.
have [delta [P [hDelta hP]]]:=@coefficient_polynomial_original_denominator A B L M BM
  embed variable coefficient embedM variableM coefficientM hB hBM
  (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi map hCoefficient hMap H.
pose chi:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
pose EL:{rmorphism B->L}:=GRing.RMorphism.clone B L (inclusion \o E) _.
have hEL:=@polynomial_evaluation_after_ring_map A B C L embed variable scalar z E inclusion hE.
have hTriangle a:chi a = phi (eta a):=esym (coefficient_fraction_scalar_triangle hCoefficient a).
have hDiagram:=@polynomial_evaluation_coefficient_extension A B M BM L
  embed variable coefficient embedM variableM coefficientM hB hBM eta map hMap
  chi phi (inclusion z) EL F hTriangle hEL hF P.
exists delta,P;split;first exact:hDelta.
apply:(fraction_field_embedding_injective hFraction).
change (inclusion (scalar delta*c) = EL P).
rewrite hDiagram hP !rmorphM (polynomial_evaluation_constants hF) hH.
by rewrite (coefficient_fraction_scalar_triangle hCoefficient).
Qed.
