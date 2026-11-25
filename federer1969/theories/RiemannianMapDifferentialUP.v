(** Federer (1969), 3.2.46, p. 282: use the actual
    coordinate differential of a map between the original
    Riemannian chart domains. Its specification depends only
    on the original map values and 3.1.1, p. 209,
    without a selected total representative or differential field. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric RiemannianTensorUP RiemannianMetricCarrier
  NormDifferentialUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [has_riemannian_map_differential]: the same
    coordinate differential Df(a) used in 3.2.46, p. 282,
    specified through an existential representative agreeing
    on the entire original chart. Only values on that
    domain enter the defining approximation of 3.1.1, p. 209. *)
Definition has_riemannian_map_differential (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (a : riemannian_metric_space hg) (D : Hom (R_n R m) (R_n R n)) :=
  exists F : R_n R m -> R_n R n,
    (forall x : riemannian_metric_space hg, F (val x)=val (f x)) /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) A F (val a) D.

(** Source for [is_riemannian_map_differential_graph]:
    independent exact partial-graph laws for the actual
    differential in 3.2.46, p. 282. No derivative,
    differentiability, area identity or coarea identity is
    assumed as part of this specification. *)
Definition is_riemannian_map_differential_graph (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (Df : partial_function (riemannian_metric_space hg) (Hom (R_n R m) (R_n R n))) :=
  forall a D, partial_function_graph Df a D <-> has_riemannian_map_differential f a D.
