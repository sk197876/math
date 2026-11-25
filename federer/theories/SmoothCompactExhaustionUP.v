(** Federer (1969), 4.1.1, p. 344: compact
    neighbourhood exhaustions support the common-support
    assertion for weakly convergent smooth-dual sequences.
    These independent laws describe an auxiliary exhaustion;
    they assume no conclusion about dual functionals. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_smooth_compact_exhaustion]: increasing
    compact subsets of U are cofinal as neighbourhoods
    of every compact subset, supporting the support
    assertion in Federer 4.1.1, p. 344. *)
Record is_smooth_compact_exhaustion (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (K:nat->smooth_compact_set hNX U):Prop:={
  (** Source for [smooth_compact_exhaustion_monotone]: the
      compact bounds increase, supporting the common
      support argument in Federer 4.1.1, p. 344. *)
  smooth_compact_exhaustion_monotone:forall m n,(m<=n)%N ->
    smooth_compact_carrier (K m) `<=` smooth_compact_carrier (K n);
  (** Source for [smooth_compact_exhaustion_neighbourhood]:
      every original compact has an open neighbourhood
      inside a sufficiently late compact bound, supporting
      Federer 4.1.1, p. 344. *)
  smooth_compact_exhaustion_neighbourhood:forall C:smooth_compact_set hNX U,
    exists n (W:set X),@open (real_norm_metric_space hNX) W /\
      smooth_compact_carrier C `<=` W /\ W `<=` smooth_compact_carrier (K n)
}.
