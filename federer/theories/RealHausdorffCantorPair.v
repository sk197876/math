(** Federer 2.10.28, pp. 191-193, especially its power-gauge application
    on p. 193. Identify the existing interval-cover measure with the
    original real-dimensional Hausdorff measure at the actual Euler-Gamma
    normalization of 2.10.2. Reuse the sealed Cantor recurrence and all
    established distribution-function conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealPower
  RealHausdorffNormalisation RealHausdorffMeasure MetricRealPowerIntervalAgreement
  ConcaveIntervalMeasure PowerCantorPairUP PowerCantorPair
  LebesgueScalarMeasure MeasureAlmostUP RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_hausdorff_interval_power_agreement]: supporting
    exact measure identification for Federer 2.10.28, pp. 191-193.
    Unrestricted covers and compact-interval covers give the same
    Gamma-normalized real-degree measure on every original subset of
    the line. Degree zero and infinite masses are included. *)
Theorem real_hausdorff_interval_power_agreement (R : realType)
    (p : R) (hp : 0<=p) (A : set (real_line_metric R)) :
    @real_hausdorff_measure R [the metricType R of real_line_metric R] p hp A=
    concave_interval_measure
      (fun t => real_hausdorff_normalisation hp * real_power t p) A.
Proof.
exact: (@metric_real_power_interval_measure_agreement R
  (real_hausdorff_normalisation hp) p
  (ltW (real_hausdorff_normalisation_positive hp)) hp A).
Qed.

(** Source for [power_cantor_pair_hausdorff_mass]: direct real-degree
    mass and cumulative-mass assertions in Federer 2.10.28, p. 193.
    Instantiate the existing power Cantor laws at alpha(m)*2^(-m).
    The measure is the actual Gamma-normalized Hausdorff measure of
    2.10.2 on each original set, including every cumulative slice. *)
Theorem power_cantor_pair_hausdorff_mass (R : realType)
    (m : R) (hm : 0<=m) n A f :
    0<m -> m<1 ->
    is_power_cantor_pair (real_hausdorff_normalisation hm) m n A f ->
    @real_hausdorff_measure R [the metricType R of real_line_metric R]
      m hm A=(real_hausdorff_normalisation hm)%:E /\
    forall x : R,
      @real_hausdorff_measure R [the metricType R of real_line_metric R]
        m hm (A `&` [set z | z<=x])=(f x)%:E.
Proof.
move=> hm0 hm1 hpair.
exact: (@power_cantor_pair_real_power_mass R
  (real_hausdorff_normalisation hm) m n A f
  (real_hausdorff_normalisation_positive hm) hm0 hm1 hpair).
Qed.

(** Source for [federer_2_10_28_real_degree]: direct complete power-gauge
    application of Federer 2.10.28, p. 193. The actual Cantor set lies
    in the unit interval, is compact and Lebesgue-null, and has Hausdorff
    mass alpha(m)*2^(-m). Its cumulative function has the printed
    increment bound, both range identities and derivative zero off the
    Cantor set and Lebesgue almost everywhere. The original schedule is
    arbitrary, with each subdivision at least two. *)
Theorem federer_2_10_28_real_degree (R : realType) (m : R)
    (hm : 0<m) (hm1 : m<1) (n : nat -> nat) :
    (forall j, (2<=n j)%N) ->
    let c := real_hausdorff_normalisation (ltW hm) in
    exists (A : set (real_line_metric R)) (f : R -> R),
      is_power_cantor_pair c m n A f /\
      compact A /\ A `<=` (`[0,1] : set (real_line_metric R)) /\
      @real_hausdorff_measure R [the metricType R of real_line_metric R]
        m (ltW hm) A=c%:E /\
      (forall x : R,
        @real_hausdorff_measure R [the metricType R of real_line_metric R]
          m (ltW hm) (A `&` [set z | z<=x])=(f x)%:E) /\
      (forall a b, a<=b -> 0<=f b-f a /\ f b-f a<=c*real_power (b-a) m) /\
      continuous (f : real_line_metric R -> real_line_metric R) /\
      f @` A=(`[0,c] : set R) /\ f @` setT=(`[0,c] : set R) /\
      lebesgue_scalar_measure A=0%E /\
      (forall x, ~A x -> has_real_curve_derivative f x 0) /\
      measure_almost_everywhere (@lebesgue_scalar_measure R)
        [set x | has_real_curve_derivative f x 0].
Proof.
move=> hn c.
have hc : 0<c := real_hausdorff_normalisation_positive (ltW hm).
have [A [f hpair]] := @power_cantor_pair_exists R c m n hc hm hm1 hn.
have hp := @power_cantor_pair_properties R c m n A f hc hm hm1 hpair.
have [hmass hcum] := @power_cantor_pair_hausdorff_mass R m (ltW hm)
  n A f hm hm1 hpair.
exists A,f; split=> //.
case: hp => hcompact [hsub [hinterval [hincr [hcont [hrangeA [hrange
  [hnull [hderiv hae]]]]]]]].
split=> //; split=> //; split=> //; split=> //; split=> //;
  split=> //; split=> //; split=> //; split=> //; split=> //.
Qed.
