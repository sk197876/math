(** Federer (1969), 4.1.1, pp. 344–345: smooth compact
    cutoffs equal to one near a given compact set support
    restriction, density and compact-support extension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_smooth_compact_cutoff]: independent smoothness,
    compact-support and neighbourhood-plateau laws for a supplied
    cutoff, supporting Federer 4.1.1, pp. 344–345, by the
    partition of unity in 3.1.13, p. 225. No construction or
    existence is part of this predicate. *)
Record is_smooth_compact_cutoff (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U K:set X) (chi:X->R):Prop:={
  (** Source for [smooth_cutoff_class]: the cutoff is globally
      smooth, supporting Federer 4.1.1, pp. 344–345. *)
  smooth_cutoff_class:norm_class_all_orders hNX (@scalar_absolute_value_norm R)
    (fun _=>True) chi;
  (** Source for [smooth_cutoff_compact]: its actual support
      is compact, supporting Federer 4.1.1, pp. 344–345. *)
  smooth_cutoff_compact:compact (@real_function_support R (real_norm_metric_space hNX) chi);
  (** Source for [smooth_cutoff_support_in_domain]: its actual
      support lies inside U, supporting the localization
      arguments of Federer 4.1.1, pp. 344–345. *)
  smooth_cutoff_support_in_domain:
    @real_function_support R (real_norm_metric_space hNX) chi `<=` U;
  (** Source for [smooth_cutoff_neighbourhood_plateau]: it is
      exactly one on an open neighbourhood of K, supporting
      the dual support arguments in Federer 4.1.1, pp. 344–345. *)
  smooth_cutoff_neighbourhood_plateau:exists W:set X,
    @open (real_norm_metric_space hNX) W /\ K `<=` W /\ forall x,W x -> chi x = 1%R
}.
