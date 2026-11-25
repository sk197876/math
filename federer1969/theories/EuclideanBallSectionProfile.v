(** Federer (1969), 2.10.27, p. 191: public auxiliary section-cost profile
    through its opaque interface. Source locators are given in
    EuclideanBallSectionProfileUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBallVolume
  EuclideanLebesgueDimensions EuclideanBallSectionProfileUP EuclideanBallSectionProfileSealed
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_ball_section_profile]: auxiliary
    section-cost profile used in 2.10.27, p. 191.
    Its implementation remains hidden behind the
    already proved abstract value and integral laws. *)
Definition euclidean_ball_section_profile (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) :=
  @EuclideanBallSectionProfile.value R m k u r hr.

(** Source for [euclidean_ball_section_profile_specification]:
    auxiliary profile value laws in 2.10.27,
    p. 191, exposed from the opaque interface. *)
Lemma euclidean_ball_section_profile_specification (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) :
  is_euclidean_ball_section_profile k u r (@euclidean_ball_section_profile R m k u r hr).
Proof. exact: EuclideanBallSectionProfile.laws. Qed.

(** Source for [euclidean_ball_section_profile_nonnegative]:
    supporting nonnegative section costs for the sum
    in 2.10.27, p. 191, derived only
    from the abstract profile specification. *)
Lemma euclidean_ball_section_profile_nonnegative (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) y :
  0<= @euclidean_ball_section_profile R m k u r hr y.
Proof.
exact: (@ball_section_profile_nonnegative R m k u r (@euclidean_ball_section_profile R m k u r hr)
  (@euclidean_ball_section_profile_specification R m k u r hr) y).
Qed.

(** Source for [euclidean_ball_section_profile_integral]: direct
    auxiliary integral in the first display of
    2.10.27, p. 191, including empty coordinate
    blocks, radius zero and degree zero. *)
Theorem euclidean_ball_section_profile_integral (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) (hr : (0<=r)%R) :
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@euclidean_ball_section_profile R m k u r hr y : extended_real_line R)))
    (euclidean_unit_ball_volume R (k+m)*r^+(k+m))%R%:E.
Proof. exact: EuclideanBallSectionProfile.integral. Qed.
