(** Federer (1969), 3.3.10, p. 296: complete original structure
    assertions on actual endpoint and positive-mass examples. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanOneCoordinate EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume
  StructureConeUP StructureProjectionKernel StructureIncidenceSets StructurePureStructure
  StructureGrassmannMeasureFacts EuclideanGrassmannProbability OrthogonalProjectionProbability
  ProductMeasure MeasureAlmostUP MeasureUP MeasureBasic MeasureAlmostBasic
  RectifiableSetUP PureUnrectifiableLaws PositiveClosedSubsets ApproximateDifferentialAffine
  WeightedCountingMeasure NonnegativeSum NonnegativeSumSupport BorelRegularMeasureUP
  MetricClosedBalls BorelClosedProjection SuslinSetUP TopologicalBorel DaniellEmptyBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_complete_incidence_conclusion]: regression
    notation for ALL conclusions of Federer 3.3.10, p. 296. This repeats
    both actual product-nullity identities, all three EVERY-projection
    assertions and the final original-source almost-everywhere identity. *)
Definition structure_complete_incidence_conclusion (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (hStructure:is_structure_measure phi):Prop:=
  let hGamma:=(@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).1 in
  let nu:=product_measure hStructure.1 hGamma in
  let S1:=@structure_first_incidence R n m phi A in
  let S2:=@structure_second_incidence R n m phi A in
  let S3:=@structure_third_incidence R n m A in
  nu S1=0 /\nu ((A `*` setT) `\` (S2 `|` S3))=0 /\
  (forall p:euclidean_projection_space R n m,
    phi [set a|S1 (a,structure_projection_kernel hmn p)]=0 /\
    euclidean_lebesgue_measure m (euclidean_projection_linear p @`
      [set a|S2 (a,structure_projection_kernel hmn p)])=0 /\
    (euclidean_projection_linear p @` [set a|S3 (a,structure_projection_kernel hmn p)]) `<=`
      [set y|~finite_set (A `&` euclidean_projection_linear p @^-1` [set y])]) /\
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|phi (A `&` [set a|~(S2 `|` S3) (a,structure_projection_kernel hmn p)])=0].

(** Source for [structure_null_source_complete_structure]: regression
    support for Federer 3.3.10, p. 296. An original Suslin null source
    is pure in every degree. Apply the complete theorem without a
    finite whole-space mass or Borel regularity premise. *)
Lemma structure_null_source_complete_structure (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (hStructure:is_structure_measure phi):
  is_suslin_set R A ->phi A=0 ->
  structure_complete_incidence_conclusion hmn A hStructure.
Proof.
move=>hA hNull.
have hPure:is_purely_measure_m_unrectifiable phi m A.
  apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hStructure.1.
  move=>F hFA _; exact:(@measure_null_subset R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)] phi hStructure.1 F A hFA hNull).
apply:(@federer_3_3_10 R n m hmn phi A hStructure hPure hA).
rewrite hNull; exact:ltry.
Qed.

(** Source for [structure_complete_nonempty_zero_dimensional]: regression
    for COMPLETE Federer 3.3.10, p. 296. The actual R^0 source is nonempty,
    the actual standing measure is zero, and both dimensions are zero. *)
Example structure_complete_nonempty_zero_dimensional (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 0) in
  let phi:set X->\bar R:=fun _=>0 in
  exists hStructure:is_structure_measure phi,
    structure_complete_incidence_conclusion (leqnn 0) setT hStructure.
Proof.
cbn zeta.
pose phi:set (inner_metric_space (@euclidean_inner_productP R 0))->\bar R:=fun _=>0.
have hStructure:is_structure_measure phi.
  split; first exact:(@daniell_zero_measure R (inner_metric_space (@euclidean_inner_productP R 0))).
  by move=>C _ T; rewrite /phi add0e.
exists hStructure; apply:structure_null_source_complete_structure; last by [].
apply:metric_borel_suslin; exact:open_borel_set openT.
Qed.

(** Source for [structure_complete_positive_unit_interval]: regression
    for COMPLETE Federer 3.3.10, p. 296. The actual closed unit-length
    line interval has Lebesgue mass one and is purely (L^1,0) unrectifiable,
    since all finite sets are null. All six original conclusions apply
    at degree zero; the original source and its actual fibres remain. *)
Example structure_complete_positive_unit_interval (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 1) in
  let phi:=@euclidean_lebesgue_measure R 1 in
  let A:=metric_closed_ball (0%R:X) (1/2)%R in
  phi A= 1 /\exists hStructure:is_structure_measure phi,
    structure_complete_incidence_conclusion (leq0n 1) A hStructure.
Proof.
cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose phi:=@euclidean_lebesgue_measure R 1.
pose A:=metric_closed_ball (0%R:X) (1/2)%R.
have hm:=euclidean_lebesgue_is_measure R 1.
have hMass:phi A= 1.
  rewrite /phi /A (@euclidean_closed_ball_normalized_volume R 1 (0%R:X) (1/2)%R (ltac:(lra)))
    euclidean_unit_ball_volume1 expr1.
  congr (EFin _); lra.
split; first exact:hMass.
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  move=>C hC; exact:(borel_regular_borel_measurable hm
    (euclidean_lebesgue_borel_regular R 1) (closed_borel_set hC)).
exists hStructure.
have hPure:is_purely_measure_m_unrectifiable phi 0 A.
  apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hm.
  move=>F _ hFinite.
  apply:(countable_null_singletons_null hm (finite_set_countable hFinite))=>x _.
  exact:positive_euclidean_singleton_null.
have hSuslin:is_suslin_set R A.
  apply:metric_borel_suslin; exact:closed_borel_set (@metric_closed_ball_closed R [the metricType R of X] (0%R:X) (1/2)%R).
apply:(@federer_3_3_10 R 1 0 (leq0n 1) phi A hStructure hPure hSuslin).
rewrite hMass; exact:ltry.
Qed.

(** Source for [structure_complete_infinite_ambient_measure]: regression
    for COMPLETE Federer 3.3.10, p. 296. The actual weighted atomic line
    measure is infinite on the whole space and every singleton except
    zero. Original A={0} has mass zero. Keep m=n=1 and all actual product,
    every-projection and almost-every-projection assertions. *)
Example structure_complete_infinite_ambient_measure (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 1) in
  let w:X->\bar R:=fun x=>if x==0%R then 0 else +oo in
  let phi:=weighted_counting_measure w in
  phi setT=+oo /\exists hStructure:is_structure_measure phi,
    structure_complete_incidence_conclusion (leqnn 1) [set (0%R:X)] hStructure.
Proof.
cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose w:X->\bar R:=fun x=>if x==0%R then 0 else +oo.
pose phi:=weighted_counting_measure w.
have hWeight x:0<=w x by rewrite /w; case:ifP=>_; [exact:lexx|exact:leey].
have hStructure:is_structure_measure phi.
  split; first exact:weighted_counting_measure_is_measure hWeight.
  move=>S _; exact:weighted_counting_measure_measurable hWeight.
have hNull:phi [set (0%R:X)]=0.
  rewrite /phi weighted_counting_measure_sum nonnegative_sum_singleton; last exact:hWeight.
  by rewrite /w eqxx.
have hOne:euclidean_one_embed (1%R:R)!=(0%R:X).
  apply/eqP=>h; have hAt:=congr1 (fun x:X=>x ord0) h.
  have hBad:(1%R:R)=0%R by move:hAt; rewrite /euclidean_one_embed !ffunE.
  have hPositive:=@ltr01 R; by rewrite hBad ltxx in hPositive.
have hWhole:phi setT=+oo.
  apply/eqP; rewrite eq_le leey /= /phi weighted_counting_measure_sum.
  have hTerm:=@nonnegative_sum_term R [the choiceType of X] setT w
    (euclidean_one_embed (1%R:R)) Logic.I.
  by rewrite /w (negbTE hOne) in hTerm.
split; first exact:hWhole.
exists hStructure; apply:structure_null_source_complete_structure; last exact:hNull.
apply:metric_borel_suslin; apply:closed_borel_set.
apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
Qed.
