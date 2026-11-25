(** Federer (1969), 3.3.19, p. 302: private intersection
    witness for the independently specified original set A. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [circular_disc_limit_exists]: existence of
    the original level intersection A, 3.3.19, p. 302.
    This is a set-existence statement, before the separate
    geometric and measure proofs. *)
Theorem circular_disc_limit_exists (R:realType)
    (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)}):
  exists A,is_circular_disc_limit H A.
Proof.
exists (\bigcap_j circular_disc_level_union H j);move=>x;split.
- move=>hx j;exact:hx j Logic.I.
- move=>hx j _;exact:hx j.
Qed.
