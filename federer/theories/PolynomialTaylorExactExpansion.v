(** Federer (1969), 3.1.11, p. 221:
    the algebraic Taylor coefficients vanish above
    the degree, reproduce the polynomial exactly,
    and recover its original coefficients at zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom Graded GradedSums SymmetricForms SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation SymmetricPolynomialInjectivity
  PolynomialFunctions PolynomialRepresentations PolynomialTaylorCoefficients
  PolynomialTaylorTransform PolynomialTaylor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ExactExpansion.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables X Y : lmodType K.
Variable P : PolynomialFunction X Y.

(** Source for [polynomial_taylor_coefficient_above_degree]:
    S_i is zero above the polynomial degree,
    as used for the vanishing derivatives
    in Federer 3.1.11, p. 221,
    from the finite contraction formula in
    1.10.4, p. 46. *)
Lemma polynomial_taylor_coefficient_above_degree i x :
  (polynomial_degree P<i)%N -> polynomial_taylor_coefficient P i x= 0.
Proof.
move=>hi; rewrite (polynomial_taylor_coefficient_formula h0) /taylor_coefficient.
apply: big1=>m hm.
have him := leq_ltn_trans hm (ltn_ord m).
have hmdeg : (i<=polynomial_degree P)%N by move:him; rewrite ltnS.
by have hh := leq_ltn_trans hmdeg hi; rewrite ltnn in hh.
Qed.

(** Source for [polynomial_taylor_formula_any_higher_order]:
    the Taylor expansion of a polynomial has
    zero remainder at every order at least
    its degree, Federer 3.1.11, p. 221.
    Adding the higher zero coefficients does
    not change the Chapter 1 finite expansion. *)
Theorem polynomial_taylor_formula_any_higher_order k a v :
  (polynomial_degree P<=k)%N ->
  P (a+v)=\sum_(i<k.+1)
    sform_polynomial_value (polynomial_taylor_coefficient P i a) v.
Proof.
move=>hk; rewrite (polynomial_taylor_formula h0).
have hn : ((polynomial_degree P).+1<=k.+1)%N by [].
rewrite (big_ord_widen k.+1
  (fun i=>sform_polynomial_value (polynomial_taylor_coefficient P i a) v) hn)
  big_mkcond.
apply: eq_bigr=>i _.
case hi: (i<(polynomial_degree P).+1)%N=> //.
have hdeg : (polynomial_degree P<i)%N by rewrite leqNgt hi.
rewrite (polynomial_taylor_coefficient_above_degree a hdeg).
by rewrite (linear0 (@sform_polynomial_value K X Y i)).
Qed.

(** Source for [polynomial_taylor_coefficient_at_zero]:
    S_i(0) is the original coefficient form,
    supporting D^i P(0)=phi_i in Federer
    3.1.11, p. 221. *)
Theorem polynomial_taylor_coefficient_at_zero i :
  polynomial_taylor_coefficient P i 0=sform_component i (polynomial_to_forms P).
Proof.
rewrite /polynomial_taylor_coefficient.
have he : symmetric_taylor_transform (polynomial_to_forms P) 0=polynomial_to_forms P.
  apply: (symmetric_polynomial_injective h0); apply: funext=>v.
  by rewrite (symmetric_taylor_transform_value h0) add0r.
by rewrite he.
Qed.
End ExactExpansion.
