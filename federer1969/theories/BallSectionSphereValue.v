(** Federer (1969), 3.2.36, p. 273: actual ball sections are constant
    on each norm sphere. This supplies the radial integrand, without a
    new selected section function or an implementation import. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanBallVolume EuclideanBallSectionProfileUP EuclideanBallSectionProfile
  BallSectionScalarIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ball_section_scalar_sphere_value]: the actual section
    profile used to evaluate the radial terms in Federer 3.2.36,
    p. 273, has value alpha(k) times (r^2-s^2)^(k/2) on a
    sphere of radius s<=r and is zero beyond r. This is exactly the
    independent inside/outside law from 2.10.27, p. 191. The closed
    endpoint is retained even for k=0, when its value is nonzero. *)
Lemma ball_section_scalar_sphere_value (R:realType) m k (r s:R) (hr:0<=r)
    (y:inner_metric_space (@euclidean_inner_productP R m)):
  inner_norm (@euclidean_inner_productP R m) y=s ->
  fine (@euclidean_ball_section_profile R m k 0 r hr y)=
    if s<=r then euclidean_unit_ball_volume R k*Num.sqrt (r^+2-s^+2)^+k else 0.
Proof.
move=>hy.
have hD:mdist (0:inner_metric_space (@euclidean_inner_productP R m)) y=s.
  by rewrite inner_metric_distanceE sub0r inner_normN hy.
have hProfile:=@euclidean_ball_section_profile_specification R m k 0 r hr.
case:(leP s r)=>hs.
- have hIn:mdist (0:inner_metric_space (@euclidean_inner_productP R m)) y<=r by rewrite hD.
  by rewrite (ball_section_profile_inside hProfile hIn) hD /fine.
- have hOut:r<mdist (0:inner_metric_space (@euclidean_inner_productP R m)) y by rewrite hD.
  by rewrite (ball_section_profile_outside hProfile hOut) /fine.
Qed.
