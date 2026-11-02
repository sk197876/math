(** Federer (1969), 2.6.5, pp. 119–120: n-dimensional Lebesgue measure is
    the Cartesian product of n copies of L^1. These abstract laws specify
    each positive dimension on the project's existing Euclidean coordinate
    space, without exposing an implementation. Stage n has dimension n+1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP MeasurePushforward ProductMeasureUP LebesgueScalarMeasure
  EuclideanCoordinateSplit EuclideanOneCoordinate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_lebesgue_family]: abstract
    finite-product laws of Federer 2.6.5, pp. 119–120.
    The successor law uses the extremal specification of
    the binary product from 2.6.1, p. 115, after the
    actual Euclidean coordinate identification. *)
Record is_euclidean_lebesgue_family (R : realType)
    (nu : forall n, set (inner_metric_space (@euclidean_inner_productP R n.+1)) -> \bar R) : Prop := {
  (** Source for [euclidean_lebesgue_measure_law]: each
      finite product is a measure, Federer 2.6.5, p. 119. *)
  euclidean_lebesgue_measure_law : forall n, is_measure (@nu n);
  (** Source for [euclidean_lebesgue_first_law]: one scalar
      factor is L^1 from 2.5.17, p. 111, as used
      in Federer 2.6.5, pp. 119–120. *)
  euclidean_lebesgue_first_law : @nu 0%N =
    measure_pushforward (@euclidean_one_embed R) (@lebesgue_scalar_measure R);
  (** Source for [euclidean_lebesgue_successor_law]: the
      induction defining finite products in Federer 2.6.5,
      p. 119. Here the first scalar coordinate is split
      from the other coordinates at each step. *)
  euclidean_lebesgue_successor_law : forall n,
    is_product_measure (@nu n) (@lebesgue_scalar_measure R)
      (measure_pushforward (@euclidean_split R n.+1) (@nu n.+1))
}.

(** Source for [euclidean_lebesgue_family_unique]: supporting
    uniqueness of the family defined by the induction in
    Federer 2.6.5, pp. 119–120. This uses binary
    product uniqueness and both coordinate inverse identities. *)
Theorem euclidean_lebesgue_family_unique (R : realType)
    (mu nu : forall n, set (inner_metric_space (@euclidean_inner_productP R n.+1)) -> \bar R) :
  is_euclidean_lebesgue_family mu -> is_euclidean_lebesgue_family nu -> mu = nu.
Proof.
move=> hm hn; apply: functional_extensionality_dep=> n; elim: n=> [|n ih].
- by rewrite (euclidean_lebesgue_first_law hm) (euclidean_lebesgue_first_law hn).
- have hp := euclidean_lebesgue_successor_law hm n.
  rewrite ih in hp.
  have he := product_measure_unique hp (euclidean_lebesgue_successor_law hn n).
  apply: funext=> A.
  have heA := congr1 (fun xi => xi ((@euclidean_join R n.+1) @^-1` A)) he.
  have hpre : (@euclidean_split R n.+1) @^-1` ((@euclidean_join R n.+1) @^-1` A) = A.
    by apply/seteqP; split=> x /=; rewrite euclidean_splitK.
  by rewrite /measure_pushforward hpre in heA.
Qed.
