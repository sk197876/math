(** Federer (1969), 3.4.5, p. 321: the actual finite
    coefficient operators in the local/global analytic example.
    Analyticity follows from finite sums and products in 3.1.24. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticConstant
  NormAnalyticScalarProducts QuadraticSubstitutionParameterCoefficients ClearedQuadraticSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Operators.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable A:set X.
Hypothesis hOpen:forall x,A x ->norm_domain_interior NX A x.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN A f).

(** Source for [quadratic_parameter_coefficient_analytic]: every
    original parameter coefficient is an actual analytic finite
    linear combination of analytic coefficient fields, supporting
    the example cited in 3.4.5, p. 321. *)
Theorem quadratic_parameter_coefficient_analytic parity order ell (f:nat->nat->X->R):
  (forall i k,AN (f i k)) ->
  AN (fun x=>quadratic_substitution_parameter_coefficient parity order ell (fun i k=>f i k x)).
Proof.
move=>hf;rewrite /quadratic_substitution_parameter_coefficient.
apply:norm_analytic_finite_scalar_sum;first exact:hOpen.
move=>i.
have hInner:AN (fun x=>\sum_(k<order.+1)
  if ((ell<=k)&&(i+2*k+parity+ell==order))%N then
    f i k x*('C(k,ell))%:R*(-1)^+(k-ell) else 0).
  apply:norm_analytic_finite_scalar_sum;first exact:hOpen.
  move=>k;case:((ell<=k)&&(i+2*k+parity+ell==order))%N.
  - apply:norm_analytic_scalar_product.
    + apply:norm_analytic_scalar_product;first exact:hf.
      exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
    + exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
  - exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen 0).
have hValue:(fun x=>\sum_(k<order.+1 | ((ell<=k)&&(i+2*k+parity+ell==order))%N)
    f i k x*('C(k,ell))%:R*(-1)^+(k-ell))=
  (fun x=>\sum_(k<order.+1) if ((ell<=k)&&(i+2*k+parity+ell==order))%N then
    f i k x*('C(k,ell))%:R*(-1)^+(k-ell) else 0).
  by apply:funext=>x;rewrite big_mkcond.
by rewrite hValue.
Qed.

(** Source for [quadratic_cleared_remainder_analytic]: the original
    finite remainder after denominator clearing is analytic
    wherever its actual coefficients are analytic, including z=0;
    supporting 3.4.5, p. 321. *)
Theorem quadratic_cleared_remainder_analytic parity order (z c:X->R) (f:nat->nat->X->R):
  AN z ->AN c ->(forall i k,AN (f i k)) ->
  AN (fun x=>quadratic_cleared_remainder parity order (z x) (c x) (fun i k=>f i k x)).
Proof.
move=>hz hc hf;rewrite /quadratic_cleared_remainder.
apply:norm_analytic_finite_scalar_sum;first exact:hOpen.
move=>ell;apply:norm_analytic_scalar_product.
- apply:norm_analytic_scalar_product;apply:norm_analytic_scalar_power;assumption.
- exact:(quadratic_parameter_coefficient_analytic parity order ell hf).
Qed.
End Operators.
