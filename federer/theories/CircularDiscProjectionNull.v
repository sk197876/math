(** Federer (1969), 3.3.19, p. 306: every original
    orthogonal line projection has zero Lebesgue outer length.
    The actual S2 section and the common conull domain remain. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  CircularTrigonometryUP CircularTrigonometrySealed RealTrigonometryUP CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscRadialMapUP PartialFunctionUP CircularDiscConicalUpperDensity CircularDiscExactMass
  StructureCone StructureConeUP StructureProjectionKernel StructurePlaneGrowth StructureIncidenceSets
  StructureConicalDensityGrowth StructureFixedProjectionAssertions StructureHausdorffNullProjection
  StructureProjectionConditions EuclideanProjectionSpace EuclideanLebesgueDimensions
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Projections.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation pi:=(@CircularTrigonometry.half_period R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.
Variable eta:nat->partial_function E E.
Hypothesis hEta:forall j,is_circular_disc_radial_map H j (eta j).

(** Source for [circular_disc_all_second_incidence_almost]:
    H1 almost every original a in A satisfies (a,V) in
    the original S2 for EVERY line plane V, as inferred
    at the start of 3.3.19, p. 306. The common
    positive conical density gives genuine infinite aperture
    growth, rather than only the negation of zero growth. *)
Theorem circular_disc_all_second_incidence_almost:
  measure_almost_everywhere_on mu A [set a:E|forall V:G (R_n R 2) 1,
    structure_plane_infinite_growth 1 mu A a V].
Proof.
have hDensity:= @circular_disc_conical_upper_density_almost R H hH A hA eta hEta.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hConstant:0<1/(2* pi) by rewrite divr_gt0 //;lra.
pose P:set E:=[set a|forall (V:G (R_n R 2) 1) (s:R),0<s ->s<1 ->
  ((1/(2* pi))%:E<=MetricDensities.upper_metric_density 1
    (MeasureRestriction.measure_restrict mu (A `&` structure_cone V a +oo s)) a)%E].
apply:(@measure_null_subset R E mu (@hausdorff_measure_is_measure R E 1) _ (A `\` P))=>//.
move=>a [ha hBad];split=>//;move=>hGood;apply:hBad=>V.
have [p hKernel]:= @StructureKernelOnto.structure_projection_kernel_onto R 2 1 (leqnSn 1) V.
have h:= @structure_positive_conical_density_infinite_growth R mu
  (@hausdorff_measure_is_measure R E 1) A p a (1/(2* pi)) hConstant.
rewrite hKernel in h;apply:h=>s hs hs1;exact:hGood V s hs hs1.
Qed.

(** Source for [circular_disc_every_projection_null]: every
    original p in O*(2,1) has L1(p(A))= 0, exactly
    the next assertion of 3.3.19, p. 306. Actual
    3.3.10 kills its original S2 section; actual
    Lipschitz projection kills the remaining H1-null source.
    Original A and its full projection are retained. *)
Theorem circular_disc_every_projection_null (p:euclidean_projection_space R 2 1):
  euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` A)= 0%E.
Proof.
have hMu:= @hausdorff_measure_is_measure R E 1.
have hStructure:is_structure_measure mu.
  split=>// S hS;apply:(@borel_regular_borel_measurable R E mu hMu
    (@hausdorff_measure_borel_regular R E 1));exact:closed_borel_set hS.
have hFinite:(mu A< +oo)%E by rewrite (@circular_disc_hausdorff_mass R H hH A hA);exact:ltry.
pose K:= structure_projection_kernel (leqnSn 1) p.
pose B2:set E:=[set a|@structure_second_incidence R 2 1 mu A (a,K)].
pose D:= A `\` B2.
have hAll:= circular_disc_all_second_incidence_almost.
have hDNull:mu D= 0%E.
  apply:(@measure_null_subset R E mu hMu _ _ _ hAll).
  move=>a [ha hBad];split=>//;move=>hGood;apply:hBad;split=>//;exact:hGood K.
have hSecond:= @structure_second_projection_section_null R 2 1 (leqnSn 1) mu A p hStructure hFinite.
have hDSubset:D `<=` A by move=>a [ha _].
have hNullImage:= @structure_hausdorff_null_projection R 2 1 A p D hDSubset hDNull.
have hCover:(euclidean_projection_linear p @` A) `<=`
    (euclidean_projection_linear p @` B2) `|` (euclidean_projection_linear p @` D).
  move=>y [a ha <-];case:(pselect (B2 a))=>hB.
  - left;by exists a.
  - right;exists a=>//;by split.
have hMeasure:= @euclidean_lebesgue_is_measure R 1.
apply/eqP;rewrite eq_le (measure_nonnegative hMeasure) andbT.
have hBound:= @measure_binary_cover R _ (@euclidean_lebesgue_measure R 1) hMeasure _ _ _ hCover.
by rewrite hSecond hNullImage adde0 in hBound.
Qed.
End Projections.
