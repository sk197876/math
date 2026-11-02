(** Public laws of the actual projection probability theta*_{n,m} used in
    Federer (1969), 2.10.5, p. 172. Use only the opaque
    invariant-probability interface. Apply the proved Suslin/Fubini argument
    to this probability, rather than assuming projected- volume
    measurability. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  OrthogonalProjectionProbabilityUP OrthogonalProjectionProbabilitySealed
  MeasureUP BorelRegularMeasureUP SuslinSetUP PartialFunctionBasic MeasurableFunctionUP
  ProjectedVolumeMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [orthogonal_projection_probability]:
    the theta*_{n,m} used in Federer 2.10.5,
    p. 172, characterized by 2.7.16(6), p. 139. *)
Definition orthogonal_projection_probability (R : realType) (n m : nat)
    (hmn : (m<=n)%N) := @OrthogonalProjectionProbability.value R n m hmn.

(** Source for [orthogonal_projection_probability_specification]:
    invariant-probability laws of theta* from Federer
    2.7.16(6), p. 139, for 2.10.5, p. 172. *)
Lemma orthogonal_projection_probability_specification (R : realType) (n m : nat)
    (hmn : (m<=n)%N) :
  is_orthogonal_projection_probability (@orthogonal_projection_probability R n m hmn).
Proof. exact: OrthogonalProjectionProbability.laws. Qed.

(** Source for [theta_star_is_measure]: supporting
    measure laws of theta* in Federer 2.10.5,
    p. 172; derived from its sealed specification. *)
Lemma theta_star_is_measure (R : realType) (n m : nat) (hmn : (m<=n)%N) :
  is_measure (@orthogonal_projection_probability R n m hmn).
Proof. exact: orthogonal_projection_probability_measure
  (orthogonal_projection_probability_specification hmn). Qed.

(** Source for [theta_star_total]: normalization of
    the probability in Federer 2.10.5, p. 172,
    from 2.7.16(6), p. 139. *)
Lemma theta_star_total (R : realType) (n m : nat) (hmn : (m<=n)%N) :
  @orthogonal_projection_probability R n m hmn setT = 1.
Proof. exact: orthogonal_projection_probability_total
  (orthogonal_projection_probability_specification hmn). Qed.

(** Source for [theta_star_borel_regular]: supporting
    Borel regularity of the actual parameter measure
    in Federer 2.10.5, p. 172. *)
Lemma theta_star_borel_regular (R : realType) (n m : nat) (hmn : (m<=n)%N) :
  is_borel_regular_measure (@orthogonal_projection_probability R n m hmn).
Proof. exact: orthogonal_projection_probability_borel_regular
  (orthogonal_projection_probability_specification hmn). Qed.

(** Source for [theta_star_projected_volume_measurable]:
    direct measurability claim in Federer 2.10.5,
    p. 172, for the actual theta* and every
    Suslin S, including unbounded S. *)
Theorem theta_star_projected_volume_measurable (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> is_measure_measurable_function
    (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projected_volume_function (m:=m) S)).
Proof.
move=> hS.
have hfin : @orthogonal_projection_probability R n m hmn setT < +oo.
  by rewrite theta_star_total ltry.
exact (@projected_volume_function_measurable R n m
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  S (@theta_star_borel_regular R n m hmn) hfin hS).
Qed.
