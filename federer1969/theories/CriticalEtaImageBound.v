(** Federer (1969), 3.4.2(8), p. 316: transfer the
    original flat increment to an actual projection chart. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerProductUP
  InnerProductLaws RealNormUP RealPower EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalManifoldChartLaws CriticalOscillation
  CriticalFiniteDerivativeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_eta_chart_increment_bound]: the estimate
    of |f(x)-f(c)| in 3.4.2(8), p. 316. The actual kernel
    containment lifts membership in p(Z) to membership in Z.
    The original eta bound and the chart Lipschitz estimate
    then give eps*M^lambda*|u-v|^lambda. Coincident source points
    satisfy the estimate separately, without a quotient by zero. *)
Theorem critical_eta_chart_increment_bound (R:realType) m mu k
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m mu) (g:R_n R mu->R_n R m)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f:R_n R m->Y) (lambda delta eps M:R) u v:
  is_critical_manifold_chart k Z S p g ->
  (euclidean_projection_linear p @` S) u ->
  (euclidean_projection_linear p @` S) v ->C (g v) ->
  (exists z,Z z /\euclidean_projection_linear p z=u-v) ->
  0<=eps ->0<=M ->0<lambda ->
  inner_norm (@euclidean_inner_productP R m) (g u-g v)<=
    M*inner_norm (@euclidean_inner_productP R mu) (u-v) ->
  M*inner_norm (@euclidean_inner_productP R mu) (u-v)<=delta ->
  (critical_eta NY Z S C f lambda delta<=eps%:E)%E ->
  NY (f (g u)-f (g v))<=eps*real_power M lambda*
    real_power (inner_norm (@euclidean_inner_productP R mu) (u-v)) lambda.
Proof.
move=>hChart hu hv hc [z [hz hProjection]] hEps hM hLambda hLip hDelta hEta.
have [hSu hPu]:=critical_chart_right_inverse hChart hu.
have [hSv hPv]:=critical_chart_right_inverse hChart hv.
have hZ:Z (g u-g v).
  have hResidual:Z (g u-g v-z).
    apply:(critical_chart_kernel hChart).
    by rewrite !linearB hPu hPv hProjection subrr.
  have hEq:g u-g v=(g u-g v-z)+z by rewrite subrK.
  rewrite hEq;exact:subspace_add hResidual hz.
case:(eqVneq (g u) (g v))=>[hEqual|hDistinct].
- rewrite hEqual subrr (real_seminorm_zero hNY.1).
  exact:mulr_ge0 (mulr_ge0 hEps (real_power_nonnegative _ _))
    (real_power_nonnegative _ _).
- have hPositive:0<inner_norm (@euclidean_inner_productP R m) (g u-g v).
    rewrite inner_norm_gt0 subr_eq0;exact:hDistinct.
  have hDist:0<inner_norm (@euclidean_inner_productP R m) (g u-g v)<=delta.
    apply/andP;split;[exact:hPositive|exact:le_trans hLip hDelta].
  have hBound:=critical_eta_increment_upper_bound hEta hSu hc hZ hDist.
  have hPower:=@real_power_monotone R
    (inner_norm (@euclidean_inner_productP R m) (g u-g v))
    (M*inner_norm (@euclidean_inner_productP R mu) (u-v)) lambda
    (ltW hPositive) hLip hLambda.
  apply:(le_trans hBound).
  have hScaled:=ler_wpM2l hEps hPower.
  by rewrite real_power_product ?inner_norm_nonnegative // mulrA in hScaled.
Qed.
