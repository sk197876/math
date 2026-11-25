(** Federer (1969), 4.1.12, p. 368: the
    actual endpoint support has only one possible
    accumulation point. An original normal one-current
    on the line supported there must vanish.
    Use the preceding exclusion of isolated support
    points and compact point-support uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces NormalCurrentsUP
  CurrentNormalPointSupportZero CurrentNormalSupportNoIsolatedPoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_normal_single_derived_support_zero]:
    if all points of K except possibly a are
    isolated in K, no nonzero original normal
    one-current on R is supported in K. This
    supports the precise dyadic endpoint obstruction in
    Federer 4.1.12, p. 368. The topological
    condition is explicit and is later proved for
    that actual endpoint set. *)
Theorem current_normal_single_derived_support_zero (R:realType) (h2:(1+1:R)!=0)
    (U:set (R_n R 1%N))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R 1%N)) U x)
    (K:set (R_n R 1%N)) (a:R_n R 1%N)
    (hIsolated:forall y,K y->y<>a->exists W:set (R_n R 1%N),
      @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 1%N))) W /\
      W y /\forall z,K z->W z->z=y)
    (T:@current_space R h2 1%N U hU 1%N):
  @is_normal_current R h2 1%N U hU 1%N T->
  @current_support R h2 1%N U hU 1%N T `<=` K->T=0.
Proof.
move=>hNormal hSupport.
apply:(@current_normal_point_support_zero R h2 U hU T a hNormal)=>y hy.
case:(pselect (y=a))=>hEqual;first exact:hEqual.
have[W [hW [hWy hUnique]]]:=hIsolated y (hSupport y hy) hEqual.
have hNo:=@current_normal_isolated_support_exclusion R h2 U hU T hNormal.1 y W hW hWy
  (fun z hz hWz=>hUnique z (hSupport z hz) hWz).
exact:False_ind _ (hNo hy).
Qed.
