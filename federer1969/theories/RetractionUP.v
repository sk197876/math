(** Federer (1969), 3.1.19, p. 231, penultimate paragraph: a
    continuous map retracts C onto D when D is a subset of C and the
    map fixes D. Its actual source and target subspaces are explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormClassZeroTopology
  MetricSubsetBackground MetricSubsetCorestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_metric_retraction]: the continuous retraction
    definition in Federer 3.1.19, p. 231, for subsets of any metric
    ambient space. Continuity is that of the actual map C to D. *)
Record is_metric_retraction (R:realType) (X:metricType R) (C D:set X) (f:X->X) : Prop := {
  (** Source for [metric_retraction_subset]: D is a subset of C,
      in the retraction definition of Federer 3.1.19, p. 231. *)
  metric_retraction_subset : D `<=` C;
  (** Source for [metric_retraction_range]: the map has values in D,
      in the retraction definition of Federer 3.1.19, p. 231. *)
  metric_retraction_range : forall x, C x -> D (f x);
  (** Source for [metric_retraction_fixed]: the restriction to D is
      identity, Federer 3.1.19, p. 231. *)
  metric_retraction_fixed : forall x, D x -> f x=x;
  (** Source for [metric_retraction_continuous]: continuity on the
      actual subspaces C and D, Federer 3.1.19, p. 231. *)
  metric_retraction_continuous : continuous
    (@metric_subset_corestriction R X (metric_subset C) D (fun x=>f (val x))
      (fun x=>@metric_retraction_range (val x) (set_valP x)))
}.

(** Source for [is_norm_class_retraction]: a retraction of class k,
    as used for psi composed with phi in Federer 3.1.19, p. 231,
    and in 3.1.20, p. 232. Class is measured in the ambient normed
    space, with the actual open domain C. *)
Record is_norm_class_retraction (R:realType) (X:lmodType R) (NX:X->R)
    (hNX:is_real_norm NX) (C D:set X) (f:X->X) k : Prop := {
  (** Source for [norm_retraction_class]: the class-k regularity in
      the local retraction of Federer 3.1.19, p. 231. *)
  norm_retraction_class : norm_class hNX hNX C f k;
  (** Source for [norm_retraction_subset]: the retract lies in its
      domain, supporting Federer 3.1.19, p. 231. *)
  norm_retraction_subset : D `<=` C;
  (** Source for [norm_retraction_range]: the map sends C to D,
      supporting the local retraction in 3.1.19, p. 231. *)
  norm_retraction_range : forall x, C x -> D (f x);
  (** Source for [norm_retraction_fixed]: points of D are fixed,
      supporting the local retraction in 3.1.19, p. 231. *)
  norm_retraction_fixed : forall x, D x -> f x=x
}.
