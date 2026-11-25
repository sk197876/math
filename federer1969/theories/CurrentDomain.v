(** Federer (1969), 4.1.7, pp. 355–358: measures
    and densities live on the original open U
    with its relative Euclidean topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [current_domain]: the original domain
    U as its actual topological subspace, supporting
    Federer 4.1.7, pp. 355–358. This transparent
    alias adds neither a point nor an extension
    outside the original domain. *)
Definition current_domain (R:realType) n (U:set (R_n R n)):topologicalType:=
  [the topologicalType of set_type
    (U:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))))].
Arguments current_domain R n U : clear implicits.
