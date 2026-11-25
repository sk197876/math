(** Federer (1969), 3.1.3(4), p. 213: translating the variable turns
    approximate continuity at u into an approximate limit at zero.
    This supporting invariance follows from the centered ball and
    Lebesgue translation laws, retaining the actual partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueTranslation EuclideanAdditiveGroup EuclideanClosedBallVolume
  EuclideanNoncenteredVitali MetricClosedBalls CenteredBallRelations
  PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasurePushforward
  MeasureSetDensity MeasureApproximateLimitUP EuclideanZeroDensitySmallMass
  CenteredZeroDensityCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section Translation.
Variable R : realType.
Variable k : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R k)).
Local Notation Leb := (@euclidean_lebesgue_measure R k).
Local Notation V := (@centered_closed_ball_relation R [the metricType R of E]).
Variables a b : E.

(** Source for [euclidean_translated_section_ball_mass]: supporting
    invariance of centered section masses for Federer 3.1.3(4), p. 213,
    by the translation invariance of 2.7.16, p. 135. *)
Lemma euclidean_translated_section_ball_mass (A : set E) r :
  Leb (((fun z : E=>(a+z)%R) @^-1` A) `&` metric_closed_ball b r)=
  Leb (A `&` metric_closed_ball (a+b)%R r).
Proof.
have hd (z : E) : mdist (a+b)%R (a+z)%R=mdist b z.
  by rewrite !inner_metric_distanceE opprD addrACA subrr add0r.
have he : ((fun z : E=>(a+z)%R) @^-1` A) `&` metric_closed_ball b r=
    (euclidean_translation a) @^-1` (A `&` metric_closed_ball (a+b)%R r).
  apply/seteqP; split.
  - move=> z [hz hbz]; split=> //.
    change (is_true (mdist (a+b)%R (a+z)%R<=r)%R); by rewrite hd.
  - move=> z [hz hbz]; split=> //.
    change (is_true (mdist (a+b)%R (a+z)%R<=r)%R) in hbz.
    by rewrite hd in hbz.
rewrite he.
exact (congr1 (fun mu : set E -> \bar R=>mu (A `&` metric_closed_ball (a+b)%R r))
  (@euclidean_lebesgue_translation_pushforward R k a)).
Qed.

(** Source for [euclidean_zero_density_translation]: density zero at
    a+b becomes density zero at b after precomposition by translation
    by a, supporting Federer 3.1.3(4), p. 213. No measurability of A
    is needed, since translation preserves outer measure itself. *)
Theorem euclidean_zero_density_translation (A : set E) :
  partial_function_graph (measure_set_density Leb V A) (a+b)%R 0 ->
  partial_function_graph (measure_set_density Leb V ((fun z : E=>(a+z)%R) @^-1` A)) b 0.
Proof.
move=> hA; apply: (@centered_small_mass_zero_density R [the metricType R of E]
  Leb _ b (euclidean_lebesgue_is_measure R k)).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
- move=> c hc; have [d [hd hs]] := euclidean_zero_density_small_mass hA hc.
  exists d; split=> // r hr hrd.
  rewrite euclidean_translated_section_ball_mass.
  have hh := hs r hr hrd.
  by rewrite (euclidean_closed_ball_normalized_volume (a+b)%R (ltW hr))
    -(euclidean_closed_ball_normalized_volume b (ltW hr)) in hh.
Qed.

(** Source for [euclidean_approximate_limit_translation]: translating
    the source point in the approximate limit of Federer 3.1.3(4),
    p. 213. Taking b=0 gives the printed expression g(u+z,v). *)
Theorem euclidean_approximate_limit_translation (Y : topologicalType)
    (f : partial_function E Y) y :
  is_measure_approximate_limit Leb V f (a+b)%R y ->
  is_measure_approximate_limit Leb V
    (partial_function_precompose (fun z : E=>(a+z)%R) f) b y.
Proof.
move=> hf W hn; rewrite partial_function_precompose_preimage preimage_setC.
exact (@euclidean_zero_density_translation (~` partial_function_preimage f W) (@hf W hn)).
Qed.
End Translation.

(** Source for [euclidean_zero_density_translation_inverse]: undoing
    the centered translation in the characteristic-function application
    of Federer 3.1.3(5), p. 213. The inverse translation restores the
    original section and its density point. *)
Theorem euclidean_zero_density_translation_inverse (R : realType) k
    (a b : inner_metric_space (@euclidean_inner_productP R k))
    (A : set (inner_metric_space (@euclidean_inner_productP R k))) :
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R k)])
    ((fun z : inner_metric_space (@euclidean_inner_productP R k)=>(a+z)%R) @^-1` A)) b 0 ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]) A) (a+b)%R 0.
Proof.
move=> hA.
pose B := (fun z : inner_metric_space (@euclidean_inner_productP R k)=>(a+z)%R) @^-1` A.
have hb : partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R k)]) B) (-a+(a+b))%R 0.
  by rewrite addKr.
have hh := @euclidean_zero_density_translation R k (-a)%R (a+b)%R B hb.
have he : (fun z : inner_metric_space (@euclidean_inner_productP R k)=>(-a+z)%R) @^-1` B=A.
  apply/seteqP; split=> z; change (A (a+(-a+z))%R->A z) ||
    change (A z->A (a+(-a+z))%R); by rewrite addNKr.
by rewrite he in hh.
Qed.
