(** Federer (1969), 3.4.8(10), p. 331:
    the original derivative-inverse relation is
    an actual polynomial multiple of W.
    Apply the already proved exact original
    polynomial kernel, with no new division. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialEvaluationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [original_polynomial_inverse_identity]:
    W'_(m+1)t_(m+1)-delta=s_(m+1)W_(m+1)
    in the original polynomial ring,
    3.4.8(10), p. 331. The multiplier
    is obtained from the original kernel
    equality, rather than assumed. *)
Theorem original_polynomial_inverse_identity (A P G:comNzRingType)
    (embed:{rmorphism A->P}) (variable:P) (E:{rmorphism A->G}) (xi:G)
    (J:{rmorphism P->G}) (I:set G) (W derivative T:P) (delta:A):
  is_commutative_polynomial_evaluation embed variable E xi J ->
  (forall H:P,I (J H) <->commutative_divides W H) ->
  I (J derivative*J T-E delta) ->
  exists S:P,derivative*T-embed delta = S*W.
Proof.
move=>hJ hKernel hRelation.
apply:(hKernel (derivative*T-embed delta)).1.
by rewrite rmorphB rmorphM (polynomial_evaluation_constants hJ).
Qed.
