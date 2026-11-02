(** Federer (1969), 3.2.29, p. 267:
    a countable family of class-one m-dimensional
    submanifolds contains H^m almost all of W. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanSubmanifoldUP
  HausdorffMeasure MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_countable_submanifold_measure_cover]:
    independent cover laws in Federer 3.2.29,
    p. 267. No family is selected globally,
    and W need not be measurable or have finite
    mass. Supporting positive classes are explicit. *)
Record is_countable_submanifold_measure_cover (R:realType) n m k
    (W:set (R_n R n)) (C:set (set (R_n R n))):Prop:={
  (** Source for [submanifold_measure_cover_countable]:
      the countable-family condition in Federer
      3.2.29, p. 267. *)
  submanifold_measure_cover_countable:countable C;
  (** Source for [submanifold_measure_cover_class]: each
      covering member is m-dimensional of the given
      class, Federer 3.2.29, p. 267; the
      numbered theorem uses class one. *)
  submanifold_measure_cover_class:forall S,C S ->@is_euclidean_submanifold R n m k S;
  (** Source for [submanifold_measure_cover_almost]: the
      union contains H^m almost all of W,
      Federer 3.2.29, p. 267. *)
  submanifold_measure_cover_almost:measure_almost_included
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W (\bigcup_(S in C) S)
}.

(** Source for [has_countable_submanifold_measure_cover]:
    existence of the countable manifold family in
    Federer 3.2.29, p. 267, separate from
    its independent laws and from their proof. *)
Definition has_countable_submanifold_measure_cover (R:realType) n m k (W:set (R_n R n)):=
  exists C,is_countable_submanifold_measure_cover m k W C.
