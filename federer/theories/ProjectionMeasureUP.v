(** Federer (1969), 2.10.4(1)–(2), p. 172: the common projected-volume gauge
    gives Gross measure on Borel generators and Caratheodory measure on open
    convex generators. Closed convex generators give the latter measure as
    well. Specify the three constructions independently. The target assumes
    positive integer m<=n; supporting natural-degree interfaces retain the
    existing zero-dimensional Lebesgue convention. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerConvex ProjectedVolumeGauge BorelCoverCostUP CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_convex_euclidean_sets]: direct generator
    family in Federer 2.10.4(2), p. 172. Unlike
    2.10.3, this passage does not exclude empty generators;
    their actual projected-volume cost is zero for m<=n. *)
Definition open_convex_euclidean_sets (R : realType) (n : nat) : choiceType :=
  [the choiceType of set_type [set A : set (inner_metric_space (@euclidean_inner_productP R n)) |
    open A /\ @is_inner_convex R (R_n R n) A]].

(** Source for [closed_convex_euclidean_sets]: direct
    alternative family in Federer 2.10.4(2), p. 172.
    Closedness refers to the given Euclidean topology,
    and convexity to the given real vector space. *)
Definition closed_convex_euclidean_sets (R : realType) (n : nat) : choiceType :=
  [the choiceType of set_type [set A : set (inner_metric_space (@euclidean_inner_productP R n)) |
    closed A /\ @is_inner_convex R (R_n R n) A]].

(** Source for [is_gross_measure]: independent covering
    specification of the Gross measure defined in Federer
    2.10.4(1), p. 172, retaining all Borel generators. *)
Definition is_gross_measure (R : realType) (n m : nat)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit
    (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
    (fun j => projected_volume_gauge m (val j)) mu.

(** Source for [is_caratheodory_projection_measure]: independent
    covering specification of Caratheodory measure in
    Federer 2.10.4(2), p. 172. The name distinguishes
    this particular measure from the general construction
    of 2.10.1. *)
Definition is_caratheodory_projection_measure (R : realType) (n m : nat)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit
    (fun j : open_convex_euclidean_sets R n => val j)
    (fun j => projected_volume_gauge m (val j)) mu.

(** Source for [is_closed_convex_projection_measure]: independent
    covering specification for the closed convex alternative
    in Federer 2.10.4(2), p. 172. Equality with
    the open convex construction is a separate theorem. *)
Definition is_closed_convex_projection_measure (R : realType) (n m : nat)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit
    (fun j : closed_convex_euclidean_sets R n => val j)
    (fun j => projected_volume_gauge m (val j)) mu.
