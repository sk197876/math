(** Federer 2.10.27, p. 191: public real-degree profile.
    The pointwise witness remains opaque; the exact integral is
    proved from its independently stated value laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealHausdorffBallCoefficient RealPower RealEuclideanBallSectionProfileUP
  RealEuclideanBallSectionProfileSealed RealBallSectionProfileIntegral
  PartialFunctionBasic MeasureIntegralUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Close Scope ereal_scope.

(** Source for [real_euclidean_ball_section_profile]: the real
    section-cost profile in the first display of Federer 2.10.27,
    p. 191, accessed through its opaque value specification. *)
Definition real_euclidean_ball_section_profile (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R):=
  @RealEuclideanBallSectionProfile.value R m k hk u r.

(** Source for [real_euclidean_ball_section_profile_specification]:
    the original exact profile values from Federer 2.10.27,
    p. 191, exposed without opening the selected witness. *)
Lemma real_euclidean_ball_section_profile_specification (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R):
  is_real_euclidean_ball_section_profile hk u r
    (@real_euclidean_ball_section_profile R m k hk u r).
Proof. exact:RealEuclideanBallSectionProfile.laws. Qed.

(** Source for [real_euclidean_ball_section_profile_nonnegative]:
    nonnegative section costs used in the covering sum of
    Federer 2.10.27, p. 191, for every real k>=0. *)
Lemma real_euclidean_ball_section_profile_nonnegative (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R) y:
  (0<=(@real_euclidean_ball_section_profile R m k hk u r y))%E.
Proof.
exact:(@real_ball_section_profile_nonnegative R m k hk u r _
  (@real_euclidean_ball_section_profile_specification R m k hk u r) y).
Qed.

(** Source for [real_euclidean_ball_section_profile_integral]: the
    exact first-display integral in Federer 2.10.27, p. 191,
    including zero degree, zero radius and empty base dimension. *)
Theorem real_euclidean_ball_section_profile_integral (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R):
  0<=r ->is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@real_euclidean_ball_section_profile R m k hk u r y:
      extended_real_line R)))
    (real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m))*real_power r (k+m%:R))%:E.
Proof.
move=> hr;exact:(@real_ball_section_profile_integral R m k hk u r _ hr
  (@real_euclidean_ball_section_profile_specification R m k hk u r)).
Qed.
