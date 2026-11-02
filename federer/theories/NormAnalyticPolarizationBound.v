(** Federer (1969), 3.1.24, p. 238: bounding
    the symmetric form of each homogeneous coefficient using
    1.10.5. The exponential constant 4 replaces e. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealNormUP SymmetricForms HomogeneousPolynomialFunctions
  PolynomialNorm SymmetricOperatorNorm PolynomialPolarizationNorm FactorialExponentialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_closed_ball_finite_norm_bound]: the
    inequality r^m ||p_m|| <= 1 in Federer 3.1.24,
    p. 238, implication (4) to (1). Scaling a
    unit-ball argument by r gives ||p_m|| <= r^(-m),
    for arbitrary normed source and target spaces. *)
Lemma polynomial_closed_ball_finite_norm_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    m (P:X->Y) r :
  @is_homogeneous_polynomial R X Y m P -> 0<r ->
  (forall v,NX v<=r -> NY (P v)<=1) ->
  (polynomial_norm hNX.1 NY P <= ((r^-1)^+m)%:E)%E.
Proof.
move=>[phi hphi] hr hb.
apply: (proj2 (polynomial_norm_bound hNX.1 NY P _))=>v hv.
have hrv:NX (r*:v)<=r.
  rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW hr)).
  have hh:=ler_wpM2l (ltW hr) hv; by rewrite mulr1 in hh.
have hh:=hb (r*:v) hrv.
have hscale:NY (P (r*:v))= r^+m*NY (P v).
  by rewrite !hphi sform_polynomial_scale_argument (real_seminorm_scale hNY.1)
    normrX (ger0_norm (ltW hr)).
rewrite hscale in hh.
have hp:0<r^+m by exact: exprn_gt0.
rewrite exprVn -div1r ler_pdivlMr // mulrC.
exact hh.
Qed.

(** Source for [norm_analytic_form_coefficient_bound]: the
    estimate ||phi_m|| <= r^(-m) e^m m! in
    Federer 3.1.24, p. 238. Polarization and the
    scalar multinomial estimate prove the sufficient bound
    (4/r)^m m!; the exponential constant is deliberately
    larger, and no extra hypothesis is added. *)
Lemma norm_analytic_form_coefficient_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    m (phi:S_m X Y m) r :
  0<r -> (forall v,NX v<=r -> NY (sform_polynomial_value phi v)<=1) ->
  (symmetric_operator_norm hNX.1 NY phi <= ((4/r)^+m*(m`!)%:R)%:E)%E.
Proof.
move=>hr hb.
have hp:@is_homogeneous_polynomial R X Y m (sform_polynomial_value phi) by exists phi.
have hn:=@polynomial_closed_ball_finite_norm_bound R X Y NX NY hNX hNY m
  (sform_polynomial_value phi) r hp hr hb.
have hh:=@polynomial_polarization_finite_norm_bound R X Y NX NY hNX hNY.1 m phi
  ((r^-1)^+m) hn.
apply: le_trans hh _; rewrite lee_fin.
have hir:0<=r^-1 by rewrite invr_ge0; exact: ltW hr.
have hbound:=ler_wpM2r (exprn_ge0 m hir) (@factorial_exponential_bound R m).
rewrite exprMn mulrAC.
exact hbound.
Qed.
