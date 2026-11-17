(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: the original simple-field diagram
    identifies the substituted polynomial evaluations.
    Apply the existing coefficient-map composition and
    evaluation laws. All field maps and polynomial
    carriers retain their independent interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp ring.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  PolynomialCoefficientMapUP PolynomialCoefficientMapLaws PolynomialMappedEvaluation PolynomialScalarComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Diagrams.
Variables K L F T:fieldType.
Variable phi:{rmorphism K->L}.
Variable inclusion:{rmorphism F->L}.
Variable scalar:{rmorphism K->F}.
Variable psi:{rmorphism L->T}.
Hypothesis hTriangle:forall a:K,inclusion (scalar a) = phi a.
Variables a b:L.
Variable t:K.
Variable z:F.
Hypothesis hZ:inclusion z = a+phi t * b.
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

(** Source for [primitive_pair_coefficient_evaluation]: the
    original g(T) keeps its value through the
    two coefficient inclusions, supporting the
    simplicity argument in 3.4.8(8), p. 330. *)
Theorem primitive_pair_coefficient_evaluation (r:T) (E:{rmorphism D->T}):
  is_commutative_polynomial_evaluation embedT variableT identity r E ->
  is_commutative_polynomial_evaluation embedK variableK kappa r
    (GRing.RMorphism.clone B T ((E \o N) \o MF) _).
Proof.
move=>hE.
pose EN:{rmorphism C->T}:=GRing.RMorphism.clone C T (E \o N) _.
pose pN:{rmorphism F->T}:=GRing.RMorphism.clone F T (identity \o rho) _.
have hEN:=@polynomial_evaluation_through_coefficient_map F C T D T embedF variableF middle
  embedT variableT target hC hD rho N hN identity r E hE.
have hBase:=@polynomial_evaluation_through_coefficient_map K B F C T embedK variableK source
  embedF variableF middle hB hC scalar MF hMF pN r EN hEN.
apply:(polynomial_evaluation_change_parameters hBase).
- move=>c;change (psi (inclusion (scalar c)) = psi (phi c));by rewrite hTriangle.
- by [].
Qed.

(** Source for [primitive_pair_substitution_evaluation]: the
    original f(z-tT) evaluates at the original
    z-t r in the containing field, supporting
    coefficient descent in 3.4.8(8), p. 330. *)
Theorem primitive_pair_substitution_evaluation (r:T) (E:{rmorphism D->T}):
  is_commutative_polynomial_evaluation embedT variableT identity r E ->
  is_commutative_polynomial_evaluation embedK variableK kappa
    (psi (inclusion z)-kappa t * r)
    (GRing.RMorphism.clone B T ((E \o N) \o A) _).
Proof.
move=>hE.
have hAN:=polynomial_evaluation_after_ring_map N hA.
have hANE:=polynomial_evaluation_after_ring_map E hAN.
constructor.
- move=>c;change (E (N (A (embedK c))) = psi (phi c)).
  have hConstant:=polynomial_evaluation_constants hANE c.
  change (E (N (A (embedK c))) = E (N (embedF (scalar c)))) in hConstant.
  rewrite hConstant.
  rewrite (@polynomial_coefficient_map_constant F C T D embedF variableF middle embedT variableT target
    hC hD rho N hN) (polynomial_evaluation_constants hE).
  change (psi (inclusion (scalar c)) = psi (phi c));by rewrite hTriangle.
- change (E (N (A variableK)) = psi (inclusion z)-kappa t * r).
  have hPoint:=polynomial_evaluation_variable hANE.
  change (E (N (A variableK)) = E (N (embedF z-embedF (scalar t)*variableF))) in hPoint.
  rewrite hPoint.
  rewrite !rmorphB !rmorphM
    !(@polynomial_coefficient_map_constant F C T D embedF variableF middle embedT variableT target hC hD rho N hN)
    (@polynomial_coefficient_map_variable F C T D embedF variableF middle embedT variableT target hC hD rho N hN)
    !(polynomial_evaluation_constants hE) (polynomial_evaluation_variable hE).
  change (psi (inclusion z)-psi (inclusion (scalar t))*r = psi (inclusion z)-psi (phi t)*r).
  by rewrite hTriangle.
Qed.

(** Source for [primitive_pair_original_root_identity]: the
    original equation z=alpha+t beta gives
    z-t beta=alpha after both field inclusions,
    the identity used in 3.4.8(8), p. 330. *)
Lemma primitive_pair_original_root_identity:
  psi (inclusion z)-kappa t * psi b = psi a.
Proof. change (psi (inclusion z)-psi (phi t)*psi b = psi a).
by rewrite hZ rmorphD rmorphM addrK. Qed.

(** Source for [primitive_pair_common_root_identity]: a
    substituted root gives an original equal pair
    sum, to which finite slope separation applies
    in the classical argument of 3.4.8(8), p. 330. *)
Lemma primitive_pair_common_root_identity (r:T):
  psi a+kappa t * psi b = (psi (inclusion z)-kappa t * r)+kappa t * r.
Proof.
rewrite subrK;change (psi a+psi (phi t)*psi b = psi (inclusion z)).
by rewrite hZ rmorphD rmorphM.
Qed.
End Diagrams.
