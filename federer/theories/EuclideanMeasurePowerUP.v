(** Federer (1969), 2.10.29, p. 195: the positive integer Cartesian powers
    of a competing measure on R^d. Specify the first factor and the
    successor product law before constructing the family. Every stage is a
    measure; density, regularity and mass conclusions are not defining
    assumptions. The dimension is written recursively to match the actual
    Euclidean block interface. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates MeasureUP MetricCartesianRectangleBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_power_dimension]: supporting
    d*(q+1) ambient dimension in the
    positive Cartesian powers of 2.10.29,
    p. 195, written as successive sums
    to match the Euclidean block maps. *)
Fixpoint euclidean_power_dimension (d q : nat) : nat :=
  match q with 0 => d | k.+1 => (euclidean_power_dimension d k+d)%N end.

(** Source for [euclidean_power_dimensionE]: supporting
    equality of the recursive dimension with
    the printed product dimension in 2.10.29,
    p. 195. Stage q represents q+1 factors. *)
Lemma euclidean_power_dimensionE d q : euclidean_power_dimension d q=(q.+1*d)%N.
Proof.
elim: q=> [|q ih]; first by rewrite /= mul1n.
by rewrite /= ih mulSn addnC.
Qed.

(** Source for [is_euclidean_measure_power_family]: abstract
    measure family and actual Euclidean successor
    product laws supporting 2.10.29, p. 195.
    The construction must prove all measure laws;
    no density or desired infinity is postulated. *)
Record is_euclidean_measure_power_family (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu)
    (lambda : forall q, set (inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension d q))) -> \bar R) : Prop := {
  (** Source for [euclidean_measure_power_first]: first
      factor of the finite product in
      2.10.29, p. 195, from 2.6.5,
      p. 119. *)
  euclidean_measure_power_first : lambda 0%N=nu;
  (** Source for [euclidean_measure_power_measure]: supporting
      measure laws at every stage of the
      Cartesian powers used in 2.10.29,
      p. 195, from 2.6.1, p. 115. *)
  euclidean_measure_power_measure : forall q, is_measure (lambda q);
  (** Source for [euclidean_measure_power_successor]: actual
      Euclidean block image of the next binary
      measure product in 2.10.29, p. 195,
      following 2.6.5, pp. 119–120. *)
  euclidean_measure_power_successor : forall q, lambda q.+1=
    paired_product_measure (fun x y=>@euclidean_block_join R (euclidean_power_dimension d q) d (x,y))
      (euclidean_measure_power_measure q) hn
}.
