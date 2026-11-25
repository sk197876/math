(** Federer (1969), 3.4.5, pp. 318–321: divided
    directional coefficients agree with the actual homogeneous
    Taylor polynomials of 3.1.11, pp. 220–221. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherSymmetricFormUP SymmetricForms HomogeneousPolynomialFunctions
  PolynomialDiagonalNorm AnalyticDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_directional_coefficient_form_value]:
    the actual divided kth directional differential is exactly
    the original homogeneous Taylor coefficient evaluated in
    that direction, supporting 3.4.5, pp. 318–321. *)
Lemma analytic_directional_coefficient_form_value (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) k v (c:X->Y) a (phi:S_m X Y k):
  A a ->@is_analytic_directional_coefficient R X Y NX NY hNX hNY A f k v c ->
  is_norm_higher_differential_form NX
    (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
    (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A f k a phi ->
  c a=sform_polynomial_value phi v.
Proof.
move=>ha hc [z [hz hPhi]].
rewrite (hc a ha z hz) sform_polynomial_diagonal_value.
congr (_*:_).
rewrite hPhi;congr (phi _).
by apply:eq_from_tnth=>i;rewrite !tnth_mktuple ffunE.
Qed.
