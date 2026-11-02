(** Federer (1969), 3.1.24, pp. 240–241: an
    analytic Taylor series may be expressed in coordinates,
    with absolute convergence on a sufficiently small sum-of-
    absolute-coordinates neighbourhood of its centre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormDifferentialUP NormHigherSymmetricFormUP SymmetricForms SymmetricMultiIndices SymmetricIndexBounds
  SymmetricDividedMonomials SymmetricMonomialTuples SymmetricOperatorNorm
  HomogeneousPolynomialFunctions PolynomialCoefficientNorm NormAnalyticUP
  NormAnalyticBoundedTaylorForms NormFiniteCoordinateBound AnalyticAbsoluteCoordinateSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_coordinate_series]: the final
    coordinate representation and absolute convergence assertion
    in Federer 3.1.24, pp. 240–241. For any finite
    unit-norm vector family choose a positive analytic constant
    large enough that the indicated coordinate neighbourhood
    lies in the actual Taylor domain. The coefficient forms
    are actual higher differentials on the original domain.
    The constant term is unrestricted; its norm is retained
    separately in the proof of absolute convergence. *)
Theorem norm_analytic_coordinate_series (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a n (v:'I_n->X) (hv:forall i,NX (v i)<=1) :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  exists (C:R) (phi:forall m,S_m X Y m),0<C /\
    (forall m,is_norm_higher_differential_form NX
      (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
      (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A f m a (phi m)) /\
    (forall m,(1<=m)%N -> (symmetric_operator_norm hNX.1 NY (phi m)<=(C^+m*(m`!)%:R)%:E)%E) /\
    forall t:'I_n->R,\sum_i `|t i|<C^-1 ->
      A (a+\sum_i t i*:v i) /\
      (forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N ->
        NY (f (a+\sum_i t i*:v i)-\sum_(m<N.+1) \sum_(b:symmetric_indices n m)
          (symmetric_scalar_monomial t (symmetric_indices_unbound b)/
            (symmetric_multi_factorial (symmetric_indices_unbound b))%:R)*:
          phi m (symmetric_monomial_tuple v b))<eps) /\
      exists B:R,forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N ->
        `|(\sum_(m<N) \sum_(b:symmetric_indices n m)
          `|symmetric_scalar_monomial t (symmetric_indices_unbound b)/
            (symmetric_multi_factorial (symmetric_indices_unbound b))%:R|*
          NY (phi m (symmetric_monomial_tuple v b)))-B|<eps.
Proof.
move=>hf.
have [U [c [phi [hc [ha [hUA [hOpen [hphi [hbound hlim]]]]]]]]]:=
  @norm_analytic_bounded_taylor_forms R X Y NX NY hNX hNY A f a hf.
have [r [hr hball]]:=hOpen a ha.
pose C:=c+1+r^-1.
have hri:0<r^-1 by rewrite invr_gt0.
have hC:0<C by rewrite /C; lra.
have hcC:c<=C by rewrite /C; lra.
have hCr:1<r*C.
  have hh:r*r^-1= 1 by rewrite mulfV // gt_eqF.
  have hpos:0<r*(c+1) by apply:mulr_gt0=>//; lra.
  rewrite /C mulrDr hh; lra.
have hCinv:C^-1<r.
  rewrite -div1r ltr_pdivrMr //; by rewrite mulrC.
have hBound m (hm:(1<=m)%N):
    (symmetric_operator_norm hNX.1 NY (phi m)<=(C^+m*(m`!)%:R)%:E)%E.
  apply:le_trans (hbound m hm) _; rewrite lee_fin.
  exact (ler_wpM2r (ler0n R (m`!)) (lerXn2r m hc (ltW hC) hcC)).
exists C,phi; split; first exact hC.
split; first exact hphi.
split; first exact hBound.
move=>t ht.
have hNorm:NX (\sum_i t i*:v i)<r.
  exact (le_lt_trans (@norm_finite_unit_coordinate_bound R X NX hNX.1 n v hv t)
    (lt_trans ht hCinv)).
have hx:U (a+\sum_i t i*:v i):=hball _ hNorm.
split; first exact (hUA _ hx).
split.
- move=>eps heps; have [k hk]:=hlim eps heps.
  exists k=>N hN.
  have hh:=hk N hN _ hx.
  have he: (\sum_(m<N.+1) sform_polynomial_value (phi m) ((a+\sum_i t i*:v i)-a))=
      \sum_(m<N.+1) \sum_(b:symmetric_indices n m)
        (symmetric_scalar_monomial t (symmetric_indices_unbound b)/
          (symmetric_multi_factorial (symmetric_indices_unbound b))%:R)*:
        phi m (symmetric_monomial_tuple v b).
    rewrite addrAC subrr add0r.
    apply:eq_bigr=>m _; exact (homogeneous_polynomial_factor_coordinates (@pchar_num R) v t (phi m)).
  by rewrite he in hh.
- have hq:C*\sum_i `|t i|<1.
    move:ht; rewrite -div1r ltr_pdivlMr //; by rewrite mulrC.
  exact (@analytic_absolute_coordinate_series R X Y NX NY hNX hNY n v hv t phi C (ltW hC) hq hBound).
Qed.
