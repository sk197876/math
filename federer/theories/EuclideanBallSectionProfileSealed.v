(** Opaque existence interface supporting Federer (1969),
    2.10.27, p. 191. The auxiliary section-volume
    construction is imported only here. Public proofs
    use its profile laws and integral, not its body.
    Source passages and edition comparisons are given
    in EuclideanBallSectionProfileUP.v and the witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBallVolume
  EuclideanLebesgueDimensions EuclideanBallSectionProfileUP EuclideanBallSectionProfileConstruction
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type EUCLIDEAN_BALL_SECTION_PROFILE.
(** Source for [value]: auxiliary profile for the
    ball-section integral in 2.10.27, p. 191,
    exposed only through its abstract value laws. *)
Parameter value : forall (R : realType) (m k : nat)
  (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R),
  (0<=r)%R -> inner_metric_space (@euclidean_inner_productP R m) -> \bar R.
(** Source for [laws]: defining inside/outside values
    of the auxiliary profile in 2.10.27, p. 191. *)
Parameter laws : forall (R : realType) (m k : nat)
  (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R),
  is_euclidean_ball_section_profile k u r (@value R m k u r hr).
(** Source for [integral]: exact auxiliary profile
    integral in the first display of 2.10.27,
    p. 191, supplied by the proved witness. *)
Parameter integral : forall (R : realType) (m k : nat)
  (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R),
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@value R m k u r hr y : extended_real_line R)))
    (euclidean_unit_ball_volume R (k+m)*r^+(k+m))%R%:E.
End EUCLIDEAN_BALL_SECTION_PROFILE.

Module EuclideanBallSectionProfile : EUCLIDEAN_BALL_SECTION_PROFILE.
(** Source for [value]: proved witness of the
    ball-section profile in 2.10.27, p. 191;
    the chosen construction is hidden by opaque ascription. *)
Definition value (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) :=
  projT1 (cid (@euclidean_ball_section_profile_exists R m k u r hr)).
(** Source for [laws]: inside/outside profile laws
    for 2.10.27, p. 191, from the proved existence witness. *)
Lemma laws (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) :
  is_euclidean_ball_section_profile k u r (@value R m k u r hr).
Proof. exact: (projT2 (cid (@euclidean_ball_section_profile_exists R m k u r hr))).1. Qed.
(** Source for [integral]: auxiliary exact integral
    for 2.10.27, p. 191, from the proved
    existence witness, without an unproved project axiom. *)
Lemma integral (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) :
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@value R m k u r hr y : extended_real_line R)))
    (euclidean_unit_ball_volume R (k+m)*r^+(k+m))%R%:E.
Proof. exact: (projT2 (cid (@euclidean_ball_section_profile_exists R m k u r hr))).2. Qed.
End EuclideanBallSectionProfile.
