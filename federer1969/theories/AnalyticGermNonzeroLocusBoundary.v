(** Federer (1969), 3.4.8(11), pp. 333–335:
    an original analytic inequality gives a functional
    stratum whose relative boundary lies in the
    original zero variety. The actual formula and
    domain are retained; no component bound is assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP FunctionalAnalyticSubmanifoldUP FunctionalAnalyticFullDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_nonzero_locus_functional_boundary]:
    the original R={y:|y|<epsilon,Phi(y)!=0}
    is a full-dimensional functional analytic submanifold;
    its boundary inside the ball lies in Phi=0,
    3.4.8(11), p. 333. *)
Theorem analytic_nonzero_locus_functional_boundary (R:realType) n (U:set (R_n R n))
    (phi:R_n R n->R^o):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) U ->
  @norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n))
    (fun z:R^o=>`|z|) (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) U phi ->
  @is_functional_analytic_submanifold R n n U [set x|U x /\phi x<>0] /\
  U `&` @closure (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    [set x|U x /\phi x<>0] `<=` [set x|U x /\phi x<>0] `|` [set x|U x /\phi x=0].
Proof.
move=>hU hPhi;split.
- apply/(functional_analytic_full_dimension U _);split;first exact:hU.
  exists phi;split;first exact:hPhi.
  by move=>x.
- move=>x [hx _];case:(pselect (phi x=0))=>hZero;[right|left];by split.
Qed.
