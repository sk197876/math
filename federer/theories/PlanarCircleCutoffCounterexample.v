(** Federer 2.10.2(1), p. 171: the actual Euclidean circle distinguishes
    open and unrestricted fixed-diameter approximations at degree one.
    Both approximations retain independent infimum specifications.
    No final measure equality is used to identify the fixed cutoffs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra ring.
From Federer Require Import FiniteCoordinates EuclideanCoordinateMetric EuclideanInnerProduct InnerNorm InnerNormInequalities InnerMetric
  PlanarUnitCircleGeometry PlanarUnitDiscLowerVolume PlanarCircleCutoffConstants
  PlanarCircleOpenGeneratorBound EuclideanBallVolume HausdorffLengthUP
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffOpenCoverAgreement
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  CaratheodoryLimitUP NonnegativeSum NonnegativeSumScale NonnegativeSumSupport
  MeasureUP MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [planar_unit_circle_diameter_at_most_two]: Federer
    2.10.2(1), p. 171; supporting actual diameter cutoff for the original
    circle generator, by the norm triangle inequality. *)
Lemma planar_unit_circle_diameter_at_most_two (R:realType):
  extended_metric_diameter (@planar_unit_circle R)<=(2:R)%:E.
Proof.
apply:(metric_diameter_least (extended_metric_diameter_specification (@planar_unit_circle R))).
- by rewrite lee_fin ler0n.
- move=>x y hx hy; rewrite lee_fin inner_metric_distanceE.
  have hh:=inner_norm_triangle (@euclidean_inner_productP R 2) x (-y)%R.
  by rewrite inner_normN hx hy in hh.
Qed.

(** Source for [planar_unit_circle_diameter_two]: Federer 2.10.2(1),
    p. 171; the actual unit circle has diameter exactly two. Opposite
    actual coordinate unit vectors attain the preceding upper bound. *)
Lemma planar_unit_circle_diameter_two (R:realType):
  extended_metric_diameter (@planar_unit_circle R) = (2:R)%:E.
Proof.
apply/eqP; rewrite eq_le planar_unit_circle_diameter_at_most_two /= .
pose u:inner_metric_space (@euclidean_inner_productP R 2):=@coordinate_basis R 2 ord0.
have hu:planar_unit_circle u:=@euclidean_coordinate_unit_norm R 2 ord0.
have hn:planar_unit_circle (-u)%R.
  change (inner_norm (@euclidean_inner_productP R 2) (-u)%R  =  1%R).
  rewrite inner_normN; exact:hu.
have hFar:(mdist u (-u)%R = 2)%R.
  rewrite inner_metric_distanceE.
  have hEq:(u- -u = 2*:u)%R.
    by rewrite opprK -{1}(scale1r u) -{2}(scale1r u) -scalerDl.
  by rewrite hEq inner_normZ (ger0_norm (_:(0<=2:>R)%R))
    ?ler0n // (hu:inner_norm (@euclidean_inner_productP R 2) u = 1%R) mulr1.
have hh:=metric_diameter_upper (extended_metric_diameter_specification (@planar_unit_circle R)) hu hn.
by rewrite hFar in hh.
Qed.

(** Source for [planar_circle_unrestricted_cutoff_upper]: Federer
    2.10.2(1), p. 171; the actual circle itself is a single admissible
    unrestricted generator of cost at most two at cutoff two. *)
Lemma planar_circle_unrestricted_cutoff_upper (R:realType)
    (phi:set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R):
  is_metric_scale_envelope
    (fun j:@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R 2))=>val j)
    (fun j=>hausdorff_diameter_cost 1 (val j)) (2:R)%:E phi ->
  phi (@planar_unit_circle R)<=(2:R)%:E.
Proof.
move=>hphi.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose A:=@planar_unit_circle R.
pose j:@nonempty_metric_sets R X:=
  @exist _ (fun B:set X=>B \in [set B|B !=set0]) A (mem_set (planar_unit_circle_nonempty R)).
have hSize k:[set j] k ->extended_metric_diameter (val k)<=(2:R)%:E.
  move=>->; exact:planar_unit_circle_diameter_at_most_two.
have hCover:A `<=` \bigcup_(k in [set j]) val k by move=>x hx; exists j.
have hh:=metric_scale_envelope_lower hphi (countable1 j) hSize hCover.
rewrite nonnegative_sum_singleton in hh; last exact:hausdorff_diameter_cost_nonnegative.
rewrite hausdorff_diameter_cost_one_degree in hh.
exact:le_trans hh (planar_unit_circle_diameter_at_most_two R).
Qed.

(** Source for [planar_circle_open_cutoff_cost_lower]: Federer
    2.10.2(1), p. 171; all actual open covers at cutoff two have total
    cost at least 2alpha(2)/coeff. Scalar constants are independent;
    their existence with coeff<alpha(2) is proved separately. *)
Lemma planar_circle_open_cutoff_cost_lower (R:realType)
    (delta radius coeff:R)
    (hc:is_planar_circle_cutoff_constants (euclidean_unit_ball_volume R 2)
      delta radius coeff)
    (G:set (@nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R 2)))):
  countable G ->
  (forall j,G j ->extended_metric_diameter (val j)<=(2:R)%:E) ->
  @planar_unit_circle R `<=` \bigcup_(j in G) val j ->
  (2*euclidean_unit_ball_volume R 2/coeff)%R%:E<=
    nonnegative_sum G (fun j=>hausdorff_diameter_cost 1 (val j)).
Proof.
move=>hG hSize hCover.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose A:=@planar_unit_circle R.
pose mu:=@hausdorff_measure R X 1.
pose F:=fun j:@nonempty_open_metric_sets R X=>A `&` val j.
pose c:=fun j:@nonempty_open_metric_sets R X=>hausdorff_diameter_cost 1 (val j).
have hPos:(0<coeff)%R:=(andP hc.2.2.2.2.2.2).1.
have hNonneg:0<=coeff%:E by rewrite lee_fin; exact:ltW hPos.
have hEach j:G j ->mu (F j)<=coeff%:E*c j.
  move=>hj; rewrite /c hausdorff_diameter_cost_one_degree.
  exact:(planar_circle_open_generator_length_bound hc (set_valP j).1 (hSize j hj)).
have hSub:A `<=` \bigcup_(j in G) F j.
  move=>x hx; have [j hj hSx]:=hCover x hx; exists j=>//; by split.
have hMass:=@measure_indexed_cover R X (@nonempty_open_metric_sets R X) mu
  (@hausdorff_measure_is_measure R X 1) A G F hG hSub.
have hSum:=nonnegative_sum_mono hEach.
have hScale:=@nonnegative_sum_scale R (@nonempty_open_metric_sets R X) G c coeff
  (ltW hPos) (fun j _=>@hausdorff_diameter_cost_nonnegative R X 1 (val j)).
rewrite hScale in hSum.
have hBound:=le_trans hMass hSum.
have hCircle:mu A = (2*euclidean_unit_ball_volume R 2)%R%:E:=planar_unit_circle_length R.
rewrite hCircle in hBound.
have hInv:0<=(coeff^-1)%R%:E by rewrite lee_fin invr_ge0; exact:ltW hPos.
have hh:=lee_wpmul2l hInv hBound.
rewrite muleA in hh.
have hCancel:(coeff^-1)%R%:E*coeff%:E = 1.
  by rewrite -EFinM mulVf ?gt_eqF.
rewrite hCancel mul1e -EFinM in hh.
have hScalar:(coeff^-1*(2*euclidean_unit_ball_volume R 2) =
    2*euclidean_unit_ball_volume R 2/coeff)%R by ring.
by rewrite hScalar in hh.
Qed.

(** Source for [federer_2_10_2_circle_cutoff_counterexample]: Federer
    2.10.2(1), p. 171, the parenthetical circle example at m = 1.
    Unrestricted cutoff value is at most two, while the open cutoff is
    strictly greater than two and finite. These are actual independently
    specified infima, without assuming either desired inequality. *)
Theorem federer_2_10_2_circle_cutoff_counterexample (R:realType)
    (phi psi:set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R):
  is_metric_scale_envelope
    (fun j:@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R 2))=>val j)
    (fun j=>hausdorff_diameter_cost 1 (val j)) (2:R)%:E phi ->
  is_metric_scale_envelope
    (fun j:@nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R 2))=>val j)
    (fun j=>hausdorff_diameter_cost 1 (val j)) (2:R)%:E psi ->
  phi (@planar_unit_circle R)<=(2:R)%:E /\
    (2:R)%:E<psi (@planar_unit_circle R) /\psi (@planar_unit_circle R)< +oo.
Proof.
move=>hphi hpsi; split; first exact:planar_circle_unrestricted_cutoff_upper hphi.
have [delta [radius [coeff hc]]]:=planar_circle_cutoff_constants_exist
  (@planar_unit_disc_volume_gt_two R).
have /andP[hPos hCoeff]:=hc.2.2.2.2.2.2.
have hLower:(2*euclidean_unit_ball_volume R 2/coeff)%R%:E<=psi (@planar_unit_circle R).
  apply:(metric_scale_envelope_greatest hpsi)=>G hG hSize hCover.
  exact:(planar_circle_open_cutoff_cost_lower hc hG hSize hCover).
have hStrict:((2:R)<2*euclidean_unit_ball_volume R 2/coeff)%R.
  rewrite (ltr_pdivlMr _ _ hPos) (ltr_pM2l (_: (0<2:>R)%R)); last by rewrite ltr0n.
  exact:hCoeff.
split; first exact:lt_le_trans (lte_tofin hStrict) hLower.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
have hTwo:0<(2:R)%:E by rewrite lte_fin ltr0n.
have hUpper:=@caratheodory_limit_upper R X (@nonempty_open_metric_sets R X)
  (fun j=>val j) (fun j=>hausdorff_diameter_cost 1 (val j))
  (@open_hausdorff_measure R X 1) (@open_hausdorff_measure_specification R X 1)
  (@planar_unit_circle R) (2:R)%:E psi hTwo hpsi.
rewrite -hausdorff_open_measure_equality planar_unit_circle_length in hUpper.
exact:le_lt_trans hUpper (ltry _).
Qed.

(** Source for [planar_circle_selected_cutoff_gap]: Federer 2.10.2(1),
    p. 171; instantiate the proved counterexample with the two actual
    opaque fixed-cutoff objects, and retain the exact circle diameter.
    No unconstrained measure or infimum witness is an extra hypothesis. *)
Theorem planar_circle_selected_cutoff_gap (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 2) in
  let phi:=metric_scale_envelope (fun j:@nonempty_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost 1 (val j)) (2:R)%:E in
  let psi:=metric_scale_envelope (fun j:@nonempty_open_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost 1 (val j)) (2:R)%:E in
  extended_metric_diameter (@planar_unit_circle R) = (2:R)%:E /\
    phi (@planar_unit_circle R)<=(2:R)%:E /\
    (2:R)%:E<psi (@planar_unit_circle R) /\psi (@planar_unit_circle R)< +oo.
Proof.
cbv zeta; split; first exact:planar_unit_circle_diameter_two.
apply:federer_2_10_2_circle_cutoff_counterexample;
  exact:metric_scale_envelope_specification.
Qed.
