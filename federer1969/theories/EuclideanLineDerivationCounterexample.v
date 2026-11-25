(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanCoordinateMetric EuclideanAffineLineGeometry EuclideanAffineLineMeasure EuclideanNoncenteredVitali
  EuclideanLebesgueDimensions LebesgueScalarMeasure HausdorffLength MeasureUP MeasureBasic MeasureAlmostBasic MeasureRestriction
  MeasureDerivationContext MeasureDerivates DerivationRatioDomain MetricClosedBalls MetricOpenShrinking
  MetricDiameterUP MetricDiameter CoveringFamilyUP CoveringFamilyLaws CoveringRelationUP CoveringRelationLimits
  NoncenteredBallRelations CoveringLowerLimitZeros MeasureInfiniteDerivatePoints PartialFunctionUP
  NullBallLocus AbsoluteContinuousPartUP AbsoluteContinuousPart AbsoluteContinuousPartBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


Section Counterexample.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Variables i j : 'I_n.
Variable v : E.
Local Notation f := (euclidean_coordinate_line i v).
Local Notation Y := (euclidean_affine_coordinate_line i v).
Local Notation psi := (euclidean_affine_line_measure i v).
Local Notation phi := (@euclidean_lebesgue_measure R n).
Local Notation V := (@noncentered_closed_ball_relation R [the metricType R of E]).

(** Source for [euclidean_line_small_zero_balls]: supporting geometric
    assertion in Federer 2.9.16, p. 161. At points of Y use tangent balls;
    outside Y use its open complement. The balls contain the point, have
    arbitrarily small diameter, and carry zero line measure. *)
Lemma euclidean_line_small_zero_balls : j != i -> forall x : E,
  forall e : R, (0<e)%R -> exists S,
    V x S /\ extended_metric_diameter S<e%:E /\ psi S=0.
Proof.
move=> hji x e he.
have hdiam (a : E) (r : R) : (0<=r)%R -> (r+r<e)%R ->
    extended_metric_diameter (metric_closed_ball a r)<e%:E.
  move=> hr hsmall.
  have hbound : extended_metric_diameter (metric_closed_ball a r)<=(r+r)%R%:E.
    apply: (@metric_diameter_least R E (metric_closed_ball a r) _
      (extended_metric_diameter_specification _) ((r+r)%R)%:E).
    - by rewrite lee_fin addr_ge0.
    - move=> y z hy hz; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hy hz.
  apply: le_lt_trans hbound _; by rewrite lte_fin.
case: (pselect (Y x))=> [[s _ <-]|hx].
- pose r := (e/3)%R.
  have hr : (0<r)%R by rewrite /r divr_gt0 // ltr0n.
  pose a : E := (f s+r*:(@coordinate_basis R n j))%R.
  have [hmem htan] := @euclidean_coordinate_tangent_ball R n i v j s r hji hr.
  exists (metric_closed_ball a r); split.
  + by exists a,r; split=> //; split.
  + split; first by apply: hdiam (ltW hr) _; rewrite /r; lra.
    rewrite euclidean_affine_line_measure_preimage.
    have heq : f @^-1` metric_closed_ball a r=[set s].
      apply/seteqP; split=> t /=.
      * move=> ht.
        have hyt : (Y `&` metric_closed_ball a r) (f t) by split=> //; exists t.
        rewrite htan in hyt.
        exact: (can_inj (@euclidean_coordinate_line_retraction R n i v)) hyt.
      * by move=> ->.
    by rewrite heq; exact: lebesgue_scalar_singleton.
- have ho : open (~` Y) := closed_openC (@euclidean_affine_coordinate_line_closed R n i v).
  have [d [hd hsub]] := @metric_open_contains_closed_ball R E (~` Y) x ho hx.
  pose r := (Num.min d (e/3))%R.
  have hr : (0<r)%R by rewrite /r lt_min hd divr_gt0 // ltr0n.
  have hrd : (r<=d)%R by rewrite /r ge_min lexx.
  have hre : (r<=e/3)%R by rewrite /r ge_min lexx orbT.
  exists (metric_closed_ball x r); split.
  + exists x,r; split=> //; split=> //.
    by rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
  + split; first by apply: hdiam (ltW hr) _; lra.
    rewrite /euclidean_affine_line_measure /measure_restrict.
    have hz : Y `&` metric_closed_ball x r=set0.
      apply/seteqP; split=> y; last by move=> [].
      move=> [hy hb]; exact: (hsub y (le_trans hb hrd)) hy.
    by rewrite hz; exact: measure_empty (@hausdorff_length_is_measure R E).
Qed.

(** Source for [euclidean_line_lower_derivate_zero]: direct
    everywhere-zero lower derivate in Federer 2.9.16,
    p. 161, for Euclidean space of any dimension at
    least two. All chosen denominator masses are positive and
    finite, so every zero ratio is an actual graph value. *)
Lemma euclidean_line_lower_derivate_zero : j != i -> forall x : E,
  covering_lower_limit V (measure_ratio_function psi phi) x=0.
Proof.
move=> hji x; apply: covering_lower_limit_zero_of_small_zero_values.
- move=> S y _ hy.
  exact: (@measure_ratio_nonnegative R E psi phi S y
    (derivation_measure_law (euclidean_affine_line_measure_class i v))
    (euclidean_lebesgue_is_measure R n) hy).
- move=> e he; have [S [hV [hd hz]]] := euclidean_line_small_zero_balls hji x he.
  exists S; split=> //; split=> //.
  have [a [r [hr [hS _]]]] := hV.
  have hp : 0<phi S by rewrite hS; exact: euclidean_closed_ball_positive hr.
  have hf : phi S \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R n) S)).
    apply: (@derivation_measure_bounded_finite R E phi (euclidean_lebesgue_derivation_class R n) S).
    rewrite hS; exact: covering_closed_ball_bounded (ltW hr).
  have hq := @measure_ratio_positive_finite_denominator R E psi phi S hp hf.
  by rewrite hz mul0e in hq.
Qed.

(** Source for [euclidean_line_continuous_part_zero]: supporting
    strengthening of psi_L^n <> psi in Federer 2.9.16,
    p. 161: the whole continuous part is zero. The
    Borel complement of the ambient-null line is an eligible
    almost cover of every set and has zero line measure. *)
Lemma euclidean_line_continuous_part_zero : j != i ->
  measure_continuous_part psi phi=(fun _ : set E => 0).
Proof.
move=> hji; apply: funext=> A; apply/eqP; rewrite eq_le.
have hspec := measure_continuous_part_specification psi phi.
have hm := derivation_measure_law (euclidean_affine_line_measure_class i v).
rewrite (continuous_part_nonnegative hm hspec A) andbT.
have hnull : phi (A `\` (~` Y))=0.
  apply: (@measure_null_subset R E phi (euclidean_lebesgue_is_measure R n) _ Y).
  - move=> x [hx hny]; exact: contrapT hny.
  - exact (@euclidean_affine_coordinate_line_null R n i v j hji).
have hzero : psi (~` Y)=0.
  rewrite /euclidean_affine_line_measure /measure_restrict setICr.
  exact: measure_empty (@hausdorff_length_is_measure R E).
rewrite -hzero.
exact: (@continuous_part_lower R E phi psi _ hspec A (~` Y)
  (borel_set_complement (euclidean_affine_coordinate_line_borel i v)) hnull).
Qed.

(** Source for [federer_2_9_16]: complete counterexample of Federer 2.9.16,
    p. 161, choosing the Euclidean norm and a coordinate straight line, with
    arbitrary translation and every finite dimension admitting i != j. The
    all-ball relation is Lebesgue Vitali; both measures belong to M; its
    lower ratio limit vanishes everywhere; the corresponding
    infinite-derivate set and null-ball locus are empty; yet the numerator
    has infinite mass on the reference-null line and differs from its
    continuous part. No claim is made for every norm: tangent balls here use
    the Euclidean inner product. *)
Theorem federer_2_9_16 : j != i ->
  is_measure_derivation_context phi V /\
  is_derivation_measure psi /\
  (forall x : E, covering_lower_limit V (measure_ratio_function psi phi) x=0) /\
  measure_infinite_derivate_points psi phi V=set0 /\
  measure_null_ball_points phi=set0 /\
  phi Y=0 /\ psi Y= +oo /\ measure_continuous_part psi phi<>psi.
Proof.
move=> hji.
have hz := euclidean_line_lower_derivate_zero hji.
split; first by constructor; [exact: euclidean_lebesgue_derivation_class|exact: euclidean_noncentered_balls_vitali].
split; first exact: euclidean_affine_line_measure_class.
split=> //; split; first exact: zero_lower_limit_infinite_derivate_points_empty hz.
split.
- apply/seteqP; split=> x; last by move=> [].
  move=> [r [hr hzero]].
  have hp := @euclidean_closed_ball_positive R n x r hr.
  by rewrite hzero ltxx in hp.
- split; first exact (@euclidean_affine_coordinate_line_null R n i v j hji).
  split; first exact: euclidean_affine_line_measure_infinite.
  move=> hid; have h := congr1 (fun g => g Y) hid.
  by move: h; rewrite (euclidean_line_continuous_part_zero hji) euclidean_affine_line_measure_infinite.
Qed.
End Counterexample.
