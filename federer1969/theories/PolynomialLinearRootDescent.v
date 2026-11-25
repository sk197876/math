(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: a linear polynomial's root belongs
    to the original coefficient field. Apply the
    existing finite-evaluation equation and field
    homomorphism laws. This is the final coefficient
    descent in the primitive-element gcd argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp ring.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialDegreeUP
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_linear_root_coefficient_descent]:
    the original linear gcd determines its root
    as the negative constant coefficient divided
    by the linear coefficient, supporting the
    classical reasoning in 3.4.8(8), p. 330.
    The nonzero denominator follows from degree one. *)
Theorem polynomial_linear_root_coefficient_descent (K:fieldType) (B:comNzRingType) (L:fieldType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism K->L}) (x:L) (E:{rmorphism B->L}) (H:B):
  is_commutative_polynomial_evaluation embed variable phi x E ->
  is_polynomial_degree coefficient H 1%N ->E H = 0 ->
    x = phi (-coefficient H 0%N/coefficient H 1%N).
Proof.
move=>hE hDegree hRoot.
have hSupport i (hi:(2<=i)%N):coefficient H i = 0:=hDegree.2 i hi.
have hEvaluation:=@polynomial_evaluation_finite_expression K B L embed variable coefficient hP phi x E hE H 2%N hSupport.
rewrite !big_ord_recr big_ord0 /= expr0 expr1 mulr1 add0r in hEvaluation.
have hSum:phi (coefficient H 0%N)+phi (coefficient H 1%N)*x = 0.
  by rewrite -hEvaluation.
have hDen:phi (coefficient H 1%N)!=0.
  rewrite fmorph_eq0;apply/eqP;exact:hDegree.1.
have hProduct:x*phi (coefficient H 1%N) = -phi (coefficient H 0%N).
  have hRestore:x*phi (coefficient H 1%N) =
      (phi (coefficient H 0%N)+phi (coefficient H 1%N)*x)-phi (coefficient H 0%N) by ring.
  by rewrite hRestore hSum sub0r.
rewrite fmorph_div rmorphN;apply:(mulIf hDen);by rewrite divfK.
Qed.
