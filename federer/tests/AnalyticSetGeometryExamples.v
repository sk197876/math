(** Federer (1969), 3.4.10, pp. 337–338:
    actual whole-plane compact mass, the nonzero R^0
    counting measure, and the cited nonanalytic singular-part
    example. Every numbered-theorem premise is proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness MetricClosedBalls
  EuclideanClosedBallCompact FiniteAnalyticVarietyBoundary AnalyticVarietyGermUP
  AnalyticRegularLocusUP FunctionalAnalyticWhole FunctionalAnalyticManifold
  HausdorffMeasure HausdorffCountingMeasure AnalyticSetGeometry BruhatWhitneySurfaceUP
  BruhatWhitneySurfaceSealed BruhatWhitneyAxis BruhatWhitneyPositiveAxisSingular
  BruhatWhitneyNegativeAxisRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_whole_plane_compact_mass_regression]:
    the actual closed unit disk has finite H^2
    mass by 3.4.10, p. 337, and every
    point of its original ambient plane is regular. *)
Example analytic_whole_plane_compact_mass_regression (R:realType):
  let hB:=@euclidean_inner_productP R 2 in
  let E:=inner_metric_space hB in
  let C:set E:=@metric_closed_ball R E 0 1 in
  @AnalyticRegularLocus.value R 2 2 setT setT=setT /\
  (@hausdorff_measure R E 2 (C `&` setT)< +oo)%E.
Proof.
move=>hB E C.
have hWhole:@is_analytic_set_in R (R_n R 2) (inner_norm hB)
    (inner_norm_real_norm hB) setT setT.
  move=>a _;exists setT,setT;split;first exact:Logic.I.
  split;last reflexivity;exact:finite_analytic_variety_domain_whole openT.
split.
- apply:funext=>a;apply:propext;split;first by move=>_.
  move=>_;apply:(@AnalyticRegularLocus.laws R 2 2 setT setT a).2.
  split;first exact:Logic.I.
  exists setT;split;first exact:openT.
  split;first exact:Logic.I.
  split;first by move=>x _.
  rewrite setIT;exact:functional_analytic_submanifold_analytic (@functional_analytic_whole R 2).
- exact:(@federer_3_4_10_compact_mass R 2 setT setT C 2 openT
    (fun _ _=>Logic.I) hWhole (@analytic_set_whole_dimension R 2)
    (@euclidean_closed_metric_ball_compact R 2 0 1) (fun _ _=>Logic.I)).
Qed.

(** Source for [analytic_zero_ambient_regular_regression]:
    the actual nonempty space R^0 is regular and
    has H^0 mass one. The separate empty-set
    totalization remains zero, at the endpoint of
    3.4.10, p. 337. *)
Example analytic_zero_ambient_regular_regression (R:realType):
  let hB:=@euclidean_inner_productP R 0 in
  let E:=inner_metric_space hB in
  @analytic_set_dimension R 0 setT=0%N /\
  @analytic_set_dimension R 0 set0=0%N /\
  @AnalyticRegularLocus.value R 0 0 setT setT=setT /\
  @hausdorff_measure R E 0 setT= 1%E.
Proof.
move=>hB E.
split;first exact:analytic_set_whole_dimension.
split;first exact:analytic_set_empty_dimension.
split.
- have hWhole:@is_analytic_set_in R (R_n R 0) (inner_norm hB)
      (inner_norm_real_norm hB) setT setT.
    move=>a _;exists setT,setT;split;first exact:Logic.I.
    split;last reflexivity;exact:finite_analytic_variety_domain_whole openT.
  exact:(@federer_3_4_10_zero_regular R 0 setT setT openT (fun _ _=>Logic.I)
    hWhole (@analytic_set_whole_dimension R 0)).
- have hPoint:(@setT E)=[set 0].
    apply:funext=>x;apply:propext;split;last by move=>_.
    move=>_;exact:coordinate_zero x.
  rewrite hPoint;exact:hausdorff_zero_singleton.
Qed.

(** Source for [analytic_nonanalytic_singular_surface_regression]:
    the original polynomial surface has a singular positive
    axis point and a regular negative axis point;
    its singular part is not analytic, as asserted
    in 3.4.10, p. 338. *)
Example analytic_nonanalytic_singular_surface_regression (R:realType):
  let S:=@BruhatWhitneySurface.set R in
  let L:=@AnalyticRegularLocus.value R 3 (@analytic_set_dimension R 3 S) setT S in
  (S `\` L) (@bruhat_whitney_axis R 1) /\
  L (@bruhat_whitney_axis R (-1)) /\
  ~@is_analytic_set_in R (R_n R 3) (inner_norm (@euclidean_inner_productP R 3))
    (inner_norm_real_norm (@euclidean_inner_productP R 3)) setT (S `\` L).
Proof.
move=>S L.
split;first by split;[exact:bruhat_whitney_axis_membership|
  exact:bruhat_whitney_positive_axis_singular ltr01].
have hNegative:(-1:R)<0 by rewrite oppr_lt0 ltr01.
split;first exact:bruhat_whitney_negative_axis_regular hNegative.
move=>hAnalytic.
exact:(@bruhat_whitney_singular_part_not_analytic_germ R (hAnalytic 0 Logic.I)).
Qed.
