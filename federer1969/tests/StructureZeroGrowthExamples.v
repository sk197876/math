(** Federer (1969), 3.3.8, p. 295: actual nonempty zero-degree,
    nonzero Lebesgue and infinite ambient-mass regressions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanLebesgueDimensions
  FiniteCoordinates StructureConeUP StructureCone StructureProjectionKernel
  StructureConeDensityUP StructurePlaneGrowth StructurePureZeroGrowth
  StructureConeDensityValues ExtendedRealBounds PositiveRightOrderLimit
  MeasureUP MeasureBasic MeasureAlmostBasic WeightedCountingMeasure NonnegativeSum NonnegativeSumSupport
  RectifiableSetUP PureUnrectifiableLaws MeasureFiniteClosure PositiveClosedSubsets ApproximateDifferentialAffine
  BernsteinNonmeasurableSubset BorelRegularMeasureUP TopologicalBorel DaniellEmptyBoundary.
From FedererTests Require Import StructurePureConeExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_zero_mass_plane_growth]: regression support
    for the original zero-growth hypothesis of Federer 3.3.8, p. 295.
    Actual zero original outer mass makes every original cone intersection
    null; the radius domain has an actual positive member. The sealed
    supremum laws give an ordinary limit, not merely an upper limit. *)
Lemma structure_zero_mass_plane_growth (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m)
    (x:inner_metric_space (@euclidean_inner_productP R n)):
  is_measure phi ->phi B=0%E ->
  structure_plane_zero_growth m phi B x (structure_projection_kernel hmn p).
Proof.
move=>hPhi hNull.
have hCost r s:structure_cone_cost hmn phi B (x,p) r s=0%E.
  have hSub:(B `&` structure_cone (structure_projection_kernel hmn p) x r%:E s) `<=` B.
    by move=>y [hy _].
  have hMass:=measure_null_subset hPhi hSub hNull.
  by rewrite /structure_cone_cost hMass !mul0e.
have hSup s:structure_plane_radial_supremum m phi B x (structure_projection_kernel hmn p) 1 s=0%E.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply:extended_real_sup_least=>v [r [_ ->]]; by rewrite -/(structure_cone_cost hmn phi B (x,p) r s) hCost.
  - rewrite -(hCost (1/2) s); apply:extended_real_sup_upper.
    exists (1/2); split; last by [].
    exact:@structure_density_positive_half_bounds R 1 ltr01.
exists 1; split; first exact:ltr01.
split.
- move=>b hb; exists 1; split; first exact:ltr01.
  move=>s hs hSmall; by rewrite hSup.
- move=>b hb; exists 1; split; first exact:ltr01.
  move=>s hs hSmall; by rewrite hSup.
Qed.

(** Source for [structure_null_source_complete_zero_growth]:
    regression setup for COMPLETE Federer 3.3.8, p. 295. The actual
    null source supplies purity and ordinary growth; apply the full
    numbered theorem with the actual original projection. *)
Lemma structure_null_source_complete_zero_growth (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->phi B=0%E ->
  is_purely_measure_m_unrectifiable phi m B /\
  (forall x,B x ->structure_plane_zero_growth m phi B x (structure_projection_kernel hmn p)) /\
  phi B=0%E.
Proof.
move=>hPhi hNull.
have hPure:is_purely_measure_m_unrectifiable phi m B.
  apply/(pure_unrectifiable_iff_rectifiable_subsets_null); split; first exact:hPhi.1.
  move=>F hFB _; exact:(@measure_null_subset R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)] phi hPhi.1 F B hFB hNull).
have hGrowth x:B x ->structure_plane_zero_growth m phi B x (structure_projection_kernel hmn p).
  move=>_; exact:structure_zero_mass_plane_growth hPhi.1 hNull.
split; first exact:hPure.
split; first exact:hGrowth.
exact:(@federer_3_3_8 R n m hmn phi B p hPhi hPure hGrowth).
Qed.

(** Source for [structure_zero_growth_nonempty_zero_dimensional]: actual
    nonempty R^0 and degree zero in COMPLETE Federer 3.3.8, p. 295.
    The standing measure is zero on the whole positive carrier. *)
Example structure_zero_growth_nonempty_zero_dimensional (R:realType):
  exists p:euclidean_projection_space R 0 0,
    let phi:set (inner_metric_space (@euclidean_inner_productP R 0))->\bar R:=fun _=>0%E in
    is_purely_measure_m_unrectifiable phi 0 setT /\
    (forall x,structure_plane_zero_growth 0 phi setT x (structure_projection_kernel (leqnn 0) p)) /\
    phi setT=0%E.
Proof.
have [p _]:=structure_mass_zero_projection_exists R 0.
exists p; cbn zeta.
pose phi:set (inner_metric_space (@euclidean_inner_productP R 0))->\bar R:=fun _=>0%E.
have hm:is_measure phi.
  constructor; first by move=>S; rewrite /phi.
  move=>A F hF hSub; rewrite /phi; exact:nonnegative_sum_nonnegative.
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  by move=>S _ T; rewrite /phi add0e.
have h:=@structure_null_source_complete_zero_growth R 0 0 (leqnn 0) phi setT p hStructure (erefl _).
by move:h=>[hPure [hGrowth hNull]]; split=>//; split=>// x; exact:hGrowth x Logic.I.
Qed.

(** Source for [structure_zero_growth_lebesgue_singleton]: actual
    nonzero line Lebesgue measure and nonempty singleton source in
    COMPLETE Federer 3.3.8, p. 295, at the degree-zero endpoint. *)
Example structure_zero_growth_lebesgue_singleton (R:realType):
  exists p:euclidean_projection_space R 1 0,
    let phi:=@euclidean_lebesgue_measure R 1 in
    let B:=[set (0:inner_metric_space (@euclidean_inner_productP R 1))] in
    is_purely_measure_m_unrectifiable phi 0 B /\
    (forall x,B x ->structure_plane_zero_growth 0 phi B x (structure_projection_kernel (leq0n 1) p)) /\
    phi B=0%E.
Proof.
have [p _]:=structure_mass_zero_projection_exists R 1; exists p; cbn zeta.
pose phi:=@euclidean_lebesgue_measure R 1.
have hm:=euclidean_lebesgue_is_measure R 1.
have hStructure:is_structure_measure phi.
  split; first exact:hm.
  move=>S hS; exact:(borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R 1) (closed_borel_set hS)).
exact:(@structure_null_source_complete_zero_growth R 1 0 (leq0n 1) phi
  [set (0:inner_metric_space (@euclidean_inner_productP R 1))] p hStructure
  (@positive_euclidean_singleton_null R 0 0)).
Qed.

(** Source for [structure_zero_growth_infinite_ambient_measure]: actual
    weighted atomic line measure, infinite on the whole space and on
    every singleton other than zero, with original B={0}, in COMPLETE
    Federer 3.3.8, p. 295. Local finiteness is not supplied. *)
Example structure_zero_growth_infinite_ambient_measure (R:realType):
  exists p:euclidean_projection_space R 1 0,
    let X:=inner_metric_space (@euclidean_inner_productP R 1) in
    let w:X->\bar R:=fun x:X=>if x==0 then 0%E else +oo%E in
    let phi:=weighted_counting_measure w in
    let B:=[set (0:X)] in
    phi setT=+oo%E /\
    is_purely_measure_m_unrectifiable phi 0 B /\
    (forall x,B x ->structure_plane_zero_growth 0 phi B x (structure_projection_kernel (leq0n 1) p)) /\
    phi B=0%E.
Proof.
have [p _]:=structure_mass_zero_projection_exists R 1; exists p; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose w:X->\bar R:=fun x:X=>if x==0 then 0%E else +oo%E.
pose phi:=weighted_counting_measure w.
have hWeight x:(0<=w x)%E by rewrite /w; case:ifP=>_; [exact:lexx|exact:leey].
have hStructure:is_structure_measure phi.
  split; first exact:weighted_counting_measure_is_measure hWeight.
  move=>S _; exact:weighted_counting_measure_measurable hWeight.
have hNull:phi [set (0:X)]=0%E.
  rewrite /phi weighted_counting_measure_sum nonnegative_sum_singleton; last exact:hWeight.
  by rewrite /w eqxx.
have hOne:euclidean_one_embed (1:R)!=(0:X).
  apply/eqP=>h; have hAt:=congr1 (fun x:X=>x ord0) h.
  have hBad:(1:R)=0 by move:hAt; rewrite /euclidean_one_embed !ffunE.
  have hPositive:=@ltr01 R; by rewrite hBad ltxx in hPositive.
have hWhole:phi setT=+oo%E.
  apply/eqP; rewrite eq_le leey /= /phi weighted_counting_measure_sum.
  have hTerm:=@nonnegative_sum_term R [the choiceType of X] setT w
    (euclidean_one_embed (1:R)) Logic.I.
  by rewrite /w (negbTE hOne) in hTerm.
split; first exact:hWhole.
exact:(@structure_null_source_complete_zero_growth R 1 0 (leq0n 1) phi [set (0:X)] p hStructure hNull).
Qed.
