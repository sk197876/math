(** Federer (1969), 3.2.46, p. 282: local coordinate
    extensions compute the actual original map differential.
    Both directions follow from locality on an open domain;
    extension values outside that domain remain irrelevant. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RiemannianTensorUP
  RiemannianMetricCarrier RiemannianMapCoordinates RiemannianMapDifferentialUP
  RiemannianMapDifferential PartialFunctionUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialEnlarge EuclideanPartitionOverlapNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_differential_local_coordinates]:
    exact agreement of the actual original Df with the
    derivative of any agreeing local representative, supporting
    3.2.46, p. 282. The original source domain, actual
    map and linear map are retained; no derivative field
    or differentiability premise is added to the conclusion. *)
Theorem riemannian_map_differential_local_coordinates (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (F : R_n R m -> R_n R n) :
  open U -> U `<=` A ->
  (forall x : riemannian_metric_space hg, U (val x) -> F (val x)=val (f x)) ->
  forall a : riemannian_metric_space hg, U (val a) -> forall D,
    (partial_function_graph (riemannian_map_differential f) a D <->
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT F (val a) D).
Proof.
move=> hU hUA hAgreement a ha D.
have hInterior := @inner_open_norm_domain R (R_n R m) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) U hU (val a) ha.
have hLocalAgreement G
    (hG : forall x : riemannian_metric_space hg, G (val x)=val (f x)) z
    (hz : U z) : G z=F z.
  pose x : riemannian_metric_space hg :=
    @exist [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
      (fun y=>y \in (A : set (inner_metric_space (@euclidean_inner_productP R m))))
      z (mem_set (hUA z hz)).
  exact (eq_trans (hG x) (esym (hAgreement x hz))).
split.
- move=> /riemannian_map_differential_graph [G [hG hD]].
  have hSmall := @norm_differential_restrict R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    A U G (val a) D hUA hInterior hD.
  have hF := @norm_differential_domain_agreement R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) U G F (val a) D
    (hLocalAgreement G hG) hSmall.
  exact (@norm_differential_enlarge R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    U setT F (val a) D (fun x _=>Logic.I) hF).
- move=> hD.
  have [G hG] := @riemannian_coordinate_representative_exists R m n A B g h hg hh f.
  have hSmall := @norm_differential_restrict R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    setT U F (val a) D (fun x _=>Logic.I) hInterior hD.
  have hGDiff := @norm_differential_domain_agreement R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) U F G (val a) D
    (fun z hz=>esym (hLocalAgreement G hG z hz)) hSmall.
  apply: (riemannian_map_differential_graph f a D).2.
  exists G; split; first exact hG.
  exact (@norm_differential_enlarge R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    U A G (val a) D hUA hGDiff).
Qed.
