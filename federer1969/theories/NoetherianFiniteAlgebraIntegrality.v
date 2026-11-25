(** Federer (1969), 3.4.8(8), p. 329:
    the original finite coefficient module gives
    integral dependence. The coefficient rings are
    already Noetherian by 3.4.7. Their finite-module
    theorem and stabilising power spans suffice;
    no determinant construction is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed CommutativePolynomialEvaluationLaws
  PolynomialBoundedEvaluationModule RingScalarRestriction RingSubmoduleUP NoetherianModuleUP
  NoetherianFiniteModule NoetherianModuleChain IntegralRingElementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_ring_module_element_integral]:
    each original element of a Noetherian coefficient
    module satisfies a monic relation, supporting
    integral dependence in 3.4.8(8), p. 329.
    The increasing bounded polynomial images stabilise. *)
Theorem noetherian_ring_module_element_integral (A C:comNzRingType)
  (phi:{rmorphism A->C}):
  is_noetherian_ring_module [the lmodType A of ring_restricted_space phi C^o] ->
    forall x:C,is_integral_ring_element phi x.
Proof.
move=>hNoetherian x.
pose P:=CommutativePolynomial.space A.
pose embed:=CommutativePolynomial.embed A.
pose variable:=CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hP:=CommutativePolynomial.laws A.
pose E:=@CommutativePolynomialEvaluation.map A P C embed variable coefficient hP phi x.
have hE:=@CommutativePolynomialEvaluation.laws A P C embed variable coefficient hP phi x.
pose V:=[the lmodType A of ring_restricted_space phi C^o].
pose M (j:nat):set V:=fun y=>exists p:P,
  (forall i,(j<=i)%N ->coefficient p i = 0) /\y = E p.
have hM j:is_ring_submodule (M j).
  exact:(@bounded_polynomial_image_submodule A P C embed variable coefficient hP phi x E hE j).
have hMono i j (hIJ:(i<=j)%N):M i `<=` M j.
  move=>y [p [hSupport hY]];exists p;split;last exact:hY.
  move=>k hJK;exact:hSupport k (leq_trans hIJ hJK).
have [N hStable]:=@noetherian_module_ascending_stabilizes A V M hNoetherian hM hMono.
have hPower:M N.+2 (x^+N.+1).
  exact:(@bounded_polynomial_image_contains_power A P C embed variable coefficient
    hP phi x E hE N.+2 N.+1 (ltnSn N.+1)).
have hIn:M N (x^+N.+1).
  rewrite -(hStable N.+2 (leq_trans (leqnSn N) (leqnSn N.+1)));exact:hPower.
have [p [hSupport hValue]]:=hIn.
exists N.+1,(coefficient p);split;first exact:ltn0Sn.
rewrite {1}hValue.
apply:(@polynomial_evaluation_finite_expression A P C embed variable coefficient hP phi x E hE p N.+1).
move=>i hi;exact:hSupport i (leq_trans (leqnSn N) hi).
Qed.

(** Source for [noetherian_finite_algebra_integral]: the
    finite extension in 3.4.8(8), p. 329,
    is integral over the original Noetherian
    coefficient ring. Apply the finite-module theorem
    already proved in 3.4.7 directly. No integral
    dependence conclusion is assumed. *)
Theorem noetherian_finite_algebra_integral (A C:comNzRingType)
  (phi:{rmorphism A->C}):
  is_noetherian_commutative_ring A ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType A of ring_restricted_space phi C^o]) ->
  forall x:C,is_integral_ring_element phi x.
Proof.
move=>hA hFinite;apply:noetherian_ring_module_element_integral.
move=>M hM.
apply:(@noetherian_submodule_of_finite_module A
  [the lmodType A of ring_restricted_space phi C^o] setT M hA hFinite hM).
by move=>x hx.
Qed.
