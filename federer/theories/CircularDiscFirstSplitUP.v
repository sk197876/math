(** Federer (1969), 3.3.19, p. 303: independent
    meaning of the first original disc level at which
    a test set meets at least two original discs. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscHitCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_circular_first_split]: the smallest
    original level meeting at least two members in
    3.3.19, p. 303. Its predecessor properties
    and existence are subsequent proved assertions. *)
Definition is_circular_first_split (R:realType)
    (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)})
    (T:set (inner_metric_space (@euclidean_inner_productP R 2))) j:Prop:=
  (2<=#|` @circular_disc_hit_indices R H j T|)%N /\
  forall i,(i<j)%N ->(#|` @circular_disc_hit_indices R H i T|<=1)%N.
