(** Federer (1969), 2.10.5, p. 172, uses the normalized invariant
    probability theta*_{n,m} of 2.7.16(6), p. 139. Specify that same measure
    independently of any choice of restricted group operations: it satisfies
    the invariant-probability laws for every such restriction. This
    paraphrases the existing invariant-measure definition, rather than
    introducing a new measure assumption. The measure laws and Borel
    regularity are consequences. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct FiniteCoordinates InnerMetric
  EuclideanOrthogonalInvariantMeasures EuclideanProjectionMetric
  IsotropyGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalInjectionSpaces
  CompactGroupHomogeneousMeasures CovariantIntegralUP MeasureUP
  SubtypeCompactHausdorff HomogeneousCovariantMeasureRadon
  BorelRegularMeasureUP RadonBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_orthogonal_projection_probability]:
    abstract specification of theta*_{n,m} in Federer
    2.7.16(6), p. 139, used in 2.10.5,
    p. 172. All restricted presentations of the same
    orthogonal group act by p composed with g inverse. *)
Definition is_orthogonal_projection_probability (R : realType) (n m : nat)
    (theta : set (orthogonal_projection_metric_space R n m) -> \bar R) : Prop :=
  forall mulS invS eS
    (hS : is_subgroup_restriction
      (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (euclidean_orthogonal_group R n) mulS invS eS),
    is_normalised_invariant_measure (orthogonal_projection_action
      (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
      (@coordinate_basisP R n) hS) theta.

(** Source for [orthogonal_projection_probability_measure]:
    supporting measure law for the theta* used in
    Federer 2.10.5, p. 172, derived from its
    invariant-probability specification. *)
Lemma orthogonal_projection_probability_measure (R : realType) (n m : nat)
    (theta : set (orthogonal_projection_metric_space R n m) -> \bar R) :
  is_orthogonal_projection_probability theta -> is_measure theta.
Proof.
move=> htheta.
have [mulS [invS [eS hS]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [[nu [_ _ hm _ _]] _] := htheta mulS invS eS hS.
exact hm.
Qed.

(** Source for [orthogonal_projection_probability_total]:
    direct normalization theta*_{n,m}(O*(n,m))=1
    from Federer 2.7.16(6), p. 139, retained
    in the gauge of 2.10.5, p. 172. *)
Lemma orthogonal_projection_probability_total (R : realType) (n m : nat)
    (theta : set (orthogonal_projection_metric_space R n m) -> \bar R) :
  is_orthogonal_projection_probability theta -> theta setT = 1%E.
Proof.
move=> htheta.
have [mulS [invS [eS hS]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
exact: (htheta mulS invS eS hS).2.
Qed.

(** Source for [orthogonal_projection_probability_borel_regular]:
    supporting Borel regularity for the product-measurability
    argument of Federer 2.10.5, p. 172. Apply
    the proved homogeneous-space Radon theorem 2.7.15,
    p. 133, and its Borel-regularity consequence.
    The required nonvanishing alternative is supplied
    by compact total mass one, without an extra premise. *)
Lemma orthogonal_projection_probability_borel_regular (R : realType) (n m : nat)
    (theta : set (orthogonal_projection_metric_space R n m) -> \bar R) :
  is_orthogonal_projection_probability theta -> is_borel_regular_measure theta.
Proof.
move=> htheta.
have [mulS [invS [eS hS]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have hthetaS := htheta mulS invS eS hS.
have hm := orthogonal_projection_probability_measure htheta.
have hc := @orthogonal_projections_compact R _ _ _ _
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) n (@coordinate_basis R n)
  (@coordinate_basisP R m) (@coordinate_basisP R n) mulS invS eS hS.
have hh := @metric_hausdorff R (orthogonal_projection_metric_space R n m).
apply: radon_borel_regular hm _.
apply: (homogeneous_covariant_measure_radon (orthogonal_group_lch hS)
  (orthogonal_projections_homogeneous (@euclidean_inner_productP R m)
    (@coordinate_basisP R m) hS) hh (compact_space_locally_compact hc) hthetaS.1).
left; exists setT; split=> //.
by rewrite hthetaS.2; exact/eqP/oner_neq0.
Qed.
