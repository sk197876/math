(** Federer (1969), 3.4.7, p. 324: the
    Lebesgue-null homogeneous polynomial zero set has
    a Hausdorff-null section on the unit sphere.
    This supporting cone lemma expands the appeal
    to polar integration in 3.2.13, p. 250,
    through its proved radial null-fibre argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormedTopology
  InnerMetric EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanRadialDifferential
  EuclideanLebesgueDimensions EuclideanBallVolume CoareaNullFibres MappingMultiplicity
  HausdorffMeasure HausdorffLipschitzImages EuclideanHausdorffDilation LipschitzUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_null_cone_unit_sphere_null]:
    the sphere-nullity step in 3.4.7, p. 324.
    An original positive cone of Lebesgue outer mass
    zero has zero H^n mass on the unit
    sphere in R^(n+1), including n=0. Neither
    source measurability nor finiteness is assumed. *)
Theorem euclidean_null_cone_unit_sphere_null (R:realType) n
    (A:set (inner_metric_space (@euclidean_inner_productP R n.+1))):
  (forall (t:R),(0<t)%R ->forall x,A x ->A (t*:x)) ->
  @euclidean_lebesgue_measure R n.+1 A = 0 ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) n
    [set x|A x /\inner_norm (@euclidean_inner_productP R n.+1) x = 1%R] = 0.
Proof.
move=>hCone hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_inner_productP R 1).
pose N:=inner_norm (@euclidean_inner_productP R n.+1).
pose H:=@hausdorff_measure R X n.
pose f:=@euclidean_radial_norm R n.+1.
have hLipschitz:is_metric_lipschitz setT f.
  exists 1%R;split;first exact:ltr01.
  exact:euclidean_radial_unit_lipschitz.
have hAlmost:=@coarea_null_source_fibres_almost_zero R 1 n f A hLipschitz hNull.
pose B:set Y:=fun y=>(inner_norm (@euclidean_inner_productP R 1)
  (y-euclidean_one_embed (2:R))<1)%R.
have hBall:@euclidean_lebesgue_measure R 1 B = (2:R)%:E.
  have hh:=@euclidean_ball_measure R 1 (euclidean_one_embed (2:R)) 1 ltr01.
  change (@euclidean_lebesgue_measure R 1 B =
    (euclidean_unit_ball_volume R 1*(1:R)^+1)%:E) in hh.
  by rewrite euclidean_unit_ball_volume1 expr1 mulr1 in hh.
have hMass:@euclidean_lebesgue_measure R 1 B<>0.
  have hp:(0<@euclidean_lebesgue_measure R 1 B)%E by rewrite hBall lte_fin ltr0n.
  move=>h;by rewrite h ltxx in hp.
have [y [hy hSlice]]:=@measure_almost_positive_set_witness R (Choice.clone Y _)
  (@euclidean_lebesgue_measure R 1) (euclidean_lebesgue_is_measure R 1)
  B [set y|H (mapping_fibre f A y) = 0] hMass hAlmost.
pose r:=euclidean_one_project y.
have hBand:(`|r-2|<1)%R.
  by move:hy;rewrite /B euclidean_one_norm_coordinate /r /euclidean_one_project
    /euclidean_one_embed !ffunE.
have hr:(0<r)%R.
  move:hBand;rewrite ltr_norml;move/andP=>[hLow hHigh];lra.
have hri:(0<r^-1)%R by rewrite invr_gt0.
have hrNonzero:(r!=0)%R by rewrite gt_eqF.
pose S:set X:=fun x=>A x /\N x = 1%R.
have hSubset:S `<=` (fun x:X=>r^-1*:x) @` mapping_fibre f A y.
  move=>x hx;exists (r*:x).
  - change (A (r*:x) /\f (r*:x) = y);split;first exact:hCone r hr x hx.1.
    change (euclidean_one_embed (N (r*:x)) = y).
    rewrite /N inner_normZ (gtr0_norm hr).
    change (euclidean_one_embed (r*N x) = y).
    rewrite hx.2 mulr1;exact:euclidean_one_projectK.
  - by rewrite scalerA (mulVf hrNonzero) scale1r.
have hTransport:=@hausdorff_positive_lipschitz_image_bound R X X
  (fun x:X=>r^-1*:x) r^-1 n hri (@euclidean_positive_dilation_lipschitz R n.+1 r^-1 hri)
  (mapping_fibre f A y).
change (H (mapping_fibre f A y) = 0) in hSlice.
change (is_true (H ((fun x:X=>r^-1*:x) @` mapping_fibre f A y)<=
  ((r^-1)^+n)%R%:E*H (mapping_fibre f A y))) in hTransport.
rewrite hSlice mule0 in hTransport.
have hMono:=@measure_mono R (Choice.clone X _) H (@hausdorff_measure_is_measure R X n)
  S ((fun x:X=>r^-1*:x) @` mapping_fibre f A y) hSubset.
apply/eqP;rewrite eq_le (measure_nonnegative (@hausdorff_measure_is_measure R X n)) andbT.
exact:le_trans hMono hTransport.
Qed.
