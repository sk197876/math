(** Federer (1969), 2.10.29, p. 195: the orthogonal regrouping of A^q*B^q
    with (A*B)^q. Specify the maps, inverse laws, squared-distance identity
    and set membership before constructing a coordinate permutation. The
    specification contains no measure equality or desired infinity
    conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanMeasurePowerUP EuclideanBlockSetPower EuclideanSetPowers EuclideanCantorProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_pair_power_shuffle_data]: abstract
    two maps in the regrouping identification
    of 2.10.29, p. 195. Stage q0
    has q=q0+1 coordinates in each scalar factor. *)
Record euclidean_pair_power_shuffle_data (R : realType) (q0 : nat) := {
  (** Source for [pair_power_shuffle_forward]: supporting
      forward map from two scalar powers
      to the Euclidean power of pairs
      in 2.10.29, p. 195. *)
  pair_power_shuffle_forward :
    (inner_metric_space (@euclidean_inner_productP R q0.+1)*inner_metric_space (@euclidean_inner_productP R q0.+1))%type ->
      inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q0));
  (** Source for [pair_power_shuffle_backward]: supporting
      inverse coordinate regrouping in 2.10.29,
      p. 195. *)
  pair_power_shuffle_backward :
    inner_metric_space (@euclidean_inner_productP R (euclidean_power_dimension 2 q0)) ->
      (inner_metric_space (@euclidean_inner_productP R q0.+1)*inner_metric_space (@euclidean_inner_productP R q0.+1))%type
}.

(** Source for [is_euclidean_pair_power_shuffle]: abstract
    inverse, orthogonal metric and membership laws
    of the identification in 2.10.29, p. 195.
    The laws must be proved by an existence
    construction before a shuffle is selected. *)
Record is_euclidean_pair_power_shuffle (R : realType) q0 (D : euclidean_pair_power_shuffle_data R q0) : Prop := {
  (** Source for [pair_power_shuffle_forwardK]: supporting
      first inverse law in 2.10.29, p. 195. *)
  pair_power_shuffle_forwardK : cancel (pair_power_shuffle_forward D) (pair_power_shuffle_backward D);
  (** Source for [pair_power_shuffle_backwardK]: supporting
      second inverse law in 2.10.29, p. 195. *)
  pair_power_shuffle_backwardK : cancel (pair_power_shuffle_backward D) (pair_power_shuffle_forward D);
  (** Source for [pair_power_shuffle_squared_distance]: supporting
      orthogonal distance identity in 2.10.29,
      p. 195. The source has the squared
      Euclidean product distance. *)
  pair_power_shuffle_squared_distance : forall p q,
    mdist (pair_power_shuffle_forward D p) (pair_power_shuffle_forward D q)^+2=
      mdist p.1 q.1^+2+mdist p.2 q.2^+2;
  (** Source for [pair_power_shuffle_membership]: direct
      Cartesian set membership identification in
      2.10.29, p. 195, for arbitrary
      scalar factor sets A and B. *)
  pair_power_shuffle_membership : forall (A B : set (real_line_metric R)) u v,
    @euclidean_block_set_power R 2 (euclidean_cantor_product A B) q0 (pair_power_shuffle_forward D (u,v)) <->
      euclidean_set_power q0.+1 A u /\ euclidean_set_power q0.+1 B v
}.
