(** Federer (1969), 3.2.46, p. 282: private existence
    of the actual map's partial coordinate differential.
    Representative agreement and the uniqueness argument
    of 3.1.1, p. 209, prove single-valuedness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RiemannianTensorUP
  RiemannianMetricCarrier RiemannianMapDifferentialUP
  NormDifferentialUP NormDifferentialLocal NormDifferentialDirectional PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_differential_graph_exists]:
    the unique actual coordinate differential defines a
    partial function, supporting 3.2.46, p. 282. The
    existence assertion selects neither a global extension
    nor a differential at a nondifferentiability point. *)
Theorem riemannian_map_differential_graph_exists (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  exists Df : partial_function (riemannian_metric_space hg) (Hom (R_n R m) (R_n R n)),
    is_riemannian_map_differential_graph f Df.
Proof.
have hUnique a D E : has_riemannian_map_differential f a D ->
    has_riemannian_map_differential f a E -> D=E.
  move=> [F [hF hD]] [G [hG hE]].
  have hAgreement z (hz : A z) : G z=F z.
    pose x : riemannian_metric_space hg :=
      @exist [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
        (fun y=>y \in (A : set (inner_metric_space (@euclidean_inner_productP R m)))) z (mem_set hz).
    exact (eq_trans (hG x) (esym (hF x))).
  have hE' := @norm_differential_domain_agreement R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) A G F (val a) E hAgreement hE.
  exact (@norm_differential_unique R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A F (val a) D E hD hE').
exists (@Build_partial_function (riemannian_metric_space hg) (Hom (R_n R m) (R_n R n))
  (has_riemannian_map_differential f) hUnique).
by move=> a D.
Qed.
