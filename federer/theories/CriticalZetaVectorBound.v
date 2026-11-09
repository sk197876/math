(** Federer (1969), 3.4.2(6), p. 312: ζ controls the derivative
    along an arbitrary tangent vector by positive normalization. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP PartialFunctionUP RelativeDifferential
  ExtendedSupremumUP RealPower CriticalOscillationUP CriticalOscillation
  CriticalRelativeDifferentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_zeta_unit_vector_bound]: the unit tangent
    test in the ζ definition, 3.4.2(4), p. 311, used in (6), p. 312.
    At a finite supremum b, every original test derivative has norm
    at most b times the indicated power of its distance from c. *)
Lemma critical_zeta_unit_vector_bound (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S C:set (R_n R m)) (f:R_n R m->Y) lambda delta b x c z
    (D:partial_function (R_n R m) Y) y:
  critical_zeta hNY Z S C f lambda delta=b%:E ->S x ->C c ->Z (x-c) ->
  0<inner_norm (@euclidean_inner_productP R m) (x-c)<=delta ->Z z ->
  inner_norm (@euclidean_inner_productP R m) z<=1 ->
  partial_function_graph (relative_norm_differential
    (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f) x D ->
  partial_function_graph D z y ->
  NY y<=b*real_power (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda.
Proof.
move=>hValue hx hc hZ hDist hz hUnit hOuter hInner.
pose P:=real_power (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda.
have hTest:critical_tangent_oscillation_values hNY Z S C f lambda delta (NY y/P).
  right;exists x,c,z,D,y;by repeat split.
have h:=extended_supremum_upper
  (@critical_zeta_laws R m Y NY hNY Z S C f lambda delta) hTest.
rewrite hValue lee_fin in h.
have hP:0<P:=@real_power_strictly_positive R _ lambda (andP hDist).1.
by rewrite (ler_pdivrMr _ _ hP) in h.
Qed.

(** Source for [critical_zeta_tangent_vector_bound]: the first
    derivative estimate along the retracted segment in 3.4.2(6),
    p. 312. Normalize a nonzero tangent vector to norm one, apply
    the original ζ test, and restore its norm by linearity of the
    actual relative differential. The zero vector is included. *)
Theorem critical_zeta_tangent_vector_bound (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S C:set (R_n R m)) (f:R_n R m->Y) lambda delta b x c z
    (D:partial_function (R_n R m) Y) y:
  critical_zeta hNY Z S C f lambda delta=b%:E ->S x ->C c ->Z (x-c) ->
  0<inner_norm (@euclidean_inner_productP R m) (x-c)<=delta ->Z z ->
  partial_function_graph (relative_norm_differential
    (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f) x D ->
  partial_function_graph D z y ->
  NY y<=inner_norm (@euclidean_inner_productP R m) z*b*
    real_power (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda.
Proof.
move=>hValue hx hc hZ hDist hz hOuter hInner.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose r:=inner_norm (@euclidean_inner_productP R m) z.
case:(eqVneq r 0)=>[hr0|hr0].
- have hz0:z=0:=hNX.2 z hr0.
  subst z.
  have hy0:=@critical_relative_differential_zero_value R (R_n R m) Y
    (inner_norm (@euclidean_inner_productP R m)) NY hNX hNY S f x D y hOuter hInner.
  by rewrite hy0 (real_seminorm_zero hNY.1) inner_norm0 !mul0r.
- have hr:0<r by rewrite lt_neqAle eq_sym hr0;exact:inner_norm_nonnegative.
  have hi:0<r^-1 by rewrite invr_gt0.
  pose u:=r^-1*:z;pose v:=r^-1*:y.
  have hu:inner_norm (@euclidean_inner_productP R m) u= 1.
    rewrite /u inner_normZ normfV (ger0_norm (ltW hr)).
    exact:(mulVf hr0).
  have hZu:Z u:=subspace_scale r^-1 hz.
  have hScaled:=@critical_relative_differential_positive_scale R (R_n R m) Y
    (inner_norm (@euclidean_inner_productP R m)) NY hNX hNY S f x D z y r^-1
    hOuter hInner (ltW hi).
  have huLe:inner_norm (@euclidean_inner_productP R m) u<=1 by rewrite hu.
  have hUnitBound:=@critical_zeta_unit_vector_bound R m Y NY hNY Z S C f lambda delta
    b x c u D v hValue hx hc hZ hDist hZu huLe hOuter hScaled.
  rewrite /v (real_seminorm_scale hNY.1) normfV (ger0_norm (ltW hr)) in hUnitBound.
  have hScaledBound:=ler_wpM2l (ltW hr) hUnitBound.
  have hCancel:r*(r^-1*NY y)=NY y by rewrite mulrA (mulfV hr0) mul1r.
  rewrite hCancel mulrA in hScaledBound.
  exact:hScaledBound.
Qed.
