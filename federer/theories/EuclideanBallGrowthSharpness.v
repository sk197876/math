(** Federer (1969), 2.9.18(2), p. 163: the complete second sharpness
    example. The reference is actual Hausdorff length restricted to an
    affine coordinate line, and the numerator is scalar Lebesgue outer
    measure of the projected set after removing that line. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanCoordinateMetric
  EuclideanAffineLineGeometry EuclideanAffineLineMeasure MetricClosedBalls MeasureUP MeasureBasic
  MeasureDerivationContext MeasureAlmostUP RadialBallRatios UpperBallRatioDichotomy
  DirectionalLimitationUP EuclideanDirectionalLimitation OffLineProjectionMeasure
  UniformBallGrowthAdequacy LineProjectionBallRatios LineReferenceSupport
  CoordinateProjection SingleCoordinateProjection PartialFunctionUP CenteredBallRatioDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

Section Example.
Variable R : realType.
Variable n : nat.
Variable i j : 'I_n.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Variable v : E.
Local Notation f := (euclidean_coordinate_line i v).
Local Notation T := (euclidean_affine_coordinate_line i v).
Local Notation phi := (euclidean_affine_line_measure i v).
Local Notation psi := (off_line_projection_measure i v).

(** Source for [line_projection_dichotomy_failure_mass]: the
    failure of the conclusion of 2.9.17 in Federer
    2.9.18(2), p. 163. Every point on T
    has upper ratio one, so the entire infinite-reference-
    mass line is an exceptional set for the zero-or-infinite
    alternative. This is stronger than mere failure on a
    nonempty set, and proves failure almost everywhere on T. *)
Lemma line_projection_dichotomy_failure_mass : j != i ->
  phi (T `\` has_zero_or_infinite_upper_ball_ratio psi phi)= +oo%E.
Proof.
move=> hji.
have he : T `\` has_zero_or_infinite_upper_ball_ratio psi phi=T.
  apply/seteqP; split=> x; first by move=> [].
  move=> hx; split=> //.
  have [s _ hs] := hx.
  move=> [hz|hz]; rewrite -hs (@line_projection_upper_ball_ratio_one R n i j v s hji) in hz.
  - by have := congr1 (fun q : \bar R => q== 0%E) hz; rewrite eqe oner_eq0 eqxx.
  - by move: hz.
by rewrite he euclidean_affine_line_measure_infinite.
Qed.

(** Source for [federer_2_9_18_2]: complete counterexample
    of Federer 2.9.18(2), p. 163, specialised to
    a valid singleton coordinate projection in O*(n,1)
    and strengthened from the printed plane to every
    dimension admitting two distinct coordinate directions.
    The Euclidean metric is proved directionally limited;
    growth with coefficient six holds on T, whose complement
    is reference-null, but no global strict growth is possible.
    The printed ball ratios are five and one, and the
    zero-or-infinite conclusion fails on all of T, of
    infinite reference mass. No Borel regularity of psi
    or global support positivity is added. *)
Theorem federer_2_9_18_2 : j != i ->
  is_derivation_measure phi /\ is_measure psi /\
  phi (~` T)= 0%E /\ psi T= 0%E /\ phi T= +oo%E /\
  O_star (GRing.Linear.clone _ _ _ _
    (@coordinate_projection R n 1 (single_coordinate_selection i)) _) /\
  (forall eta : R, 0<eta<=1/3 -> exists zeta : nat,
    @is_directionally_limited_at R [the metricType R of E] setT +oo%E eta zeta) /\
  (forall mu : R, has_uniform_fivefold_ball_growth phi T mu 6) /\
  (forall lambda mu : R, 0<mu -> ~has_uniform_fivefold_ball_growth phi setT mu lambda) /\
  (forall x, T x -> forall r : R, 0<r ->
    (phi (metric_closed_ball x (5*r))/phi (metric_closed_ball x r))%E= 5%E /\
    (psi (metric_closed_ball x r)/phi (metric_closed_ball x r))%E= 1%E /\
    centered_ball_ratio_upper_limit psi phi x= 1%E) /\
  phi (T `\` has_zero_or_infinite_upper_ball_ratio psi phi)= +oo%E.
Proof.
move=> hji; split; first exact: euclidean_affine_line_measure_class.
split; first exact: off_line_projection_is_measure.
split; first exact: line_reference_complement_null.
split; first exact: off_line_projection_target_null.
split; first exact: euclidean_affine_line_measure_infinite.
split; first exact: single_coordinate_projection_orthogonal.
split; first exact: euclidean_directional_limitation.
split; first by move=> mu; exact: line_reference_growth_on_support.
split; first by move=> lambda mu hmu; exact (@line_reference_growth_not_global R n i j v lambda mu hji hmu).
split; last exact: line_projection_dichotomy_failure_mass hji.
move=> x [s _ <-] r hr; split; first exact: line_reference_fivefold_ball_ratio hr.
split; last exact (@line_projection_upper_ball_ratio_one R n i j v s hji).
have hactual := @centered_ball_ratio_positive_domain R E phi psi (f s) r
  (euclidean_affine_line_measure_class i v)
  (@line_reference_no_null_ball_on_line R n i v s) hr.
exact (partial_function_single_valued hactual
  (@line_projection_centered_ball_ratio R n i j v s r hji hr)).
Qed.
End Example.
