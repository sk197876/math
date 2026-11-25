(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: original polynomial values agree
    through the simple-field diagram. Apply evaluation
    uniqueness to the previously proved diagram laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationLaws PolynomialCoefficientMapUP
  PolynomialScalarComposition PrimitivePairEvaluationDiagrams.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Values.
Variables K L F T:fieldType.
Variable phi:{rmorphism K->L}.
Variable inclusion:{rmorphism F->L}.
Variable scalar:{rmorphism K->F}.
Variable psi:{rmorphism L->T}.
Hypothesis hTriangle:forall a:K,inclusion (scalar a) = phi a.
Variables a b:L.
Variable t:K.
Variable z:F.
Hypothesis hZ:inclusion z = a+phi t*b.
Local Notation rho:=(GRing.RMorphism.clone F T (psi \o inclusion) _).
Local Notation kappa:=(GRing.RMorphism.clone K T (psi \o phi) _).
Local Notation identity:=(GRing.RMorphism.clone T T idfun _).
Variables B C D:comNzRingType.
Variable embedK:{rmorphism K->B}.
Variable variableK:B.
Variable source:B->nat->K.
Hypothesis hB:is_commutative_polynomial_ring embedK variableK source.
Variable embedF:{rmorphism F->C}.
Variable variableF:C.
Variable middle:C->nat->F.
Hypothesis hC:is_commutative_polynomial_ring embedF variableF middle.
Variable embedT:{rmorphism T->D}.
Variable variableT:D.
Variable target:D->nat->T.
Hypothesis hD:is_commutative_polynomial_ring embedT variableT target.
Variable MF:{rmorphism B->C}.
Hypothesis hMF:is_polynomial_coefficient_map source middle scalar MF.
Variable N:{rmorphism C->D}.
Hypothesis hN:is_polynomial_coefficient_map middle target rho N.
Variable A:{rmorphism B->C}.
Hypothesis hA:is_commutative_polynomial_evaluation embedK variableK
  (GRing.RMorphism.clone K C (embedF \o scalar) _)
  (embedF z-embedF (scalar t)*variableF) A.

(** Source for [primitive_pair_coefficient_original_value]:
    original evaluation at beta is preserved by
    both inclusions in the primitive-element argument
    invoked in 3.4.8(8), p. 330. *)
Theorem primitive_pair_coefficient_original_value (Eb:{rmorphism B->L})
  (E:{rmorphism D->T}):
  is_commutative_polynomial_evaluation embedK variableK phi b Eb ->
  is_commutative_polynomial_evaluation embedT variableT identity (psi b) E ->
  forall P:B,E (N (MF P)) = psi (Eb P).
Proof.
move=>hEb hE P.
have hLeft:=@primitive_pair_coefficient_evaluation K L F T phi inclusion scalar psi hTriangle
  B C D embedK variableK source hB embedF variableF middle hC
  embedT variableT target hD MF hMF N hN (psi b) E hE.
have hRight:=polynomial_evaluation_after_ring_map psi hEb.
exact:(@polynomial_evaluation_unique K B T embedK variableK source hB kappa (psi b)
  (GRing.RMorphism.clone B T ((E \o N) \o MF) _)
  (GRing.RMorphism.clone B T (psi \o Eb) _) hLeft hRight P).
Qed.

(** Source for [primitive_pair_substitution_value]: the
    substituted polynomial has the original value
    at z-t r in the containing field,
    the root comparison in 3.4.8(8), p. 330. *)
Theorem primitive_pair_substitution_value (r:T) (E:{rmorphism D->T})
  (Eu:{rmorphism B->T}):
  is_commutative_polynomial_evaluation embedT variableT identity r E ->
  is_commutative_polynomial_evaluation embedK variableK kappa
    (psi (inclusion z)-kappa t*r) Eu ->
  forall P:B,E (N (A P)) = Eu P.
Proof.
move=>hE hEu P.
have hLeft:=@primitive_pair_substitution_evaluation K L F T phi inclusion scalar psi hTriangle
  t z B C D embedK variableK embedF variableF middle hC
  embedT variableT target hD N hN A hA r E hE.
exact:(@polynomial_evaluation_unique K B T embedK variableK source hB kappa
  (psi (inclusion z)-kappa t*r)
  (GRing.RMorphism.clone B T ((E \o N) \o A) _) Eu hLeft hEu P).
Qed.

(** Source for [primitive_pair_substitution_original_value]:
    at the original beta, the substituted f
    evaluates at the original alpha, as in
    the primitive-element argument of 3.4.8(8), p. 330. *)
Theorem primitive_pair_substitution_original_value (Ea:{rmorphism B->L})
  (E:{rmorphism D->T}):
  is_commutative_polynomial_evaluation embedK variableK phi a Ea ->
  is_commutative_polynomial_evaluation embedT variableT identity (psi b) E ->
  forall P:B,E (N (A P)) = psi (Ea P).
Proof.
move=>hEa hE P.
have hOriginal:=@primitive_pair_original_root_identity K L F T phi inclusion psi a b t z hZ.
have hRight:=polynomial_evaluation_after_ring_map psi hEa.
have hRightAt:is_commutative_polynomial_evaluation embedK variableK kappa
  (psi (inclusion z)-kappa t*psi b) (GRing.RMorphism.clone B T (psi \o Ea) _).
  by rewrite hOriginal.
exact:(primitive_pair_substitution_value hE hRightAt P).
Qed.
End Values.
