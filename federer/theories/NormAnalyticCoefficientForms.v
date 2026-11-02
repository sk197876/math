(** Federer (1969), 3.1.24, p. 238: choosing
    the unique symmetric forms representing the homogeneous
    coefficients and proving their finite operator bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import RealNormUP SymmetricForms HomogeneousPolynomialFunctions
  PolynomialNorm SymmetricOperatorNorm PolynomialPolarizationNorm
  ContinuousSymmetricFormAdapter NormAnalyticPolarizationBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_coefficients_bounded_forms]: the
    forms phi_m chosen in implication (4) to (1),
    Federer 3.1.24, p. 238. Their existence follows
    from the homogeneous-polynomial predicate; all continuity
    bounds are proved. Positive degrees satisfy (4/r)^m m!
    in place of the printed (e/r)^m m!. The constant
    degree is bounded separately and imposes no restriction
    on the value of the function at the centre. *)
Theorem norm_analytic_coefficients_bounded_forms (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (P:nat->X->Y) r :
  (forall m,@is_homogeneous_polynomial R X Y m (P m)) -> 0<r ->
  (forall m,(1<=m)%N -> forall v,NX v<=r -> NY (P m v)<=1) ->
  exists phi:forall m,S_m X Y m,
    (forall m,P m =1 sform_polynomial_value (phi m)) /\
    (forall m,norm_bounded_symmetric_form NX NY (phi m)) /\
    forall m,(1<=m)%N ->
      (symmetric_operator_norm hNX.1 NY (phi m)<=((4/r)^+m*(m`!)%:R)%:E)%E.
Proof.
move=>hP hr hb.
pose phi m:=projT1 (cid (hP m)).
have hphi m:=projT2 (cid (hP m)).
have hpos m (hm:(1<=m)%N):
    (symmetric_operator_norm hNX.1 NY (phi m)<=((4/r)^+m*(m`!)%:R)%:E)%E.
  apply: (@norm_analytic_form_coefficient_bound R X Y NX NY hNX hNY m (phi m) r hr).
  move=>v hv; rewrite -hphi; exact (hb m hm v hv).
exists phi; split; first exact hphi.
split; last exact hpos.
move=>[|m].
- have hc x:sform_polynomial_value (phi 0%N) x= sform_polynomial_value (phi 0%N) 0.
    have hh:=sform_polynomial_scale_argument (phi 0%N) (0:R) x.
    by rewrite scale0r expr0 scale1r in hh.
  have hn:(polynomial_norm hNX.1 NY (sform_polynomial_value (phi 0%N))<=
      (NY (sform_polynomial_value (phi 0%N) 0))%:E)%E.
    apply: (proj2 (polynomial_norm_bound hNX.1 NY _ _))=>x _.
    by rewrite hc.
  have hform:=@polynomial_polarization_finite_norm_bound R X Y NX NY hNX hNY.1
    0%N (phi 0%N) (NY (sform_polynomial_value (phi 0%N) 0)) hn.
  exact (@finite_operator_norm_sform_bounded R 0%N X Y NX NY hNX hNY (phi 0%N)
    ((0%:R:R)^+0*NY (sform_polynomial_value (phi 0%N) 0)) hform).
- exact (@finite_operator_norm_sform_bounded R m.+1 X Y NX NY hNX hNY (phi m.+1)
    ((4/r)^+m.+1*((m.+1)`!)%:R) (hpos m.+1 (leq0n m))).
Qed.
