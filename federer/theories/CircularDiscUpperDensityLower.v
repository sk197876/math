(** Federer (1969), 3.3.19, p. 306: the lower
    inequality in the asserted upper-density value one half.
    It holds at every point of the original A. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscLevelPieces CircularDiscPieceHausdorffMass
  HausdorffMeasure MeasureUP MeasureBasic MeasureRestriction MetricDensities EuclideanBallVolume
  PositiveRadiusLimits ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Density.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_piece_density_lower]: the
    whole original level piece through a is contained in
    B(a,2 rho_n), and its exact mass is 2 rho_n.
    Thus the actual original ball ratio is at least one
    half at those radii, supporting 3.3.19, p. 306. *)
Lemma circular_disc_piece_density_lower (a:E) j:A a ->
  (((1:R)/2)%:E<=metric_ball_density 1 (measure_restrict mu A) a (2* rho j))%E.
Proof.
move=>ha.
have [z [hz haZ]]:=(hA a).1 ha j.
have hPositive:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hs j.
have hSubset:(A `&` metric_closed_ball z (rho j)) `<=`
    (A `&` metric_closed_ball a (2* rho j)).
  move=>x [hxA hxZ];split=>//.
  exact:(@circular_disc_within_ball_distance R j z a x haZ hxZ).
have hMass:= @measure_mono R E mu (@hausdorff_measure_is_measure R E 1) _ _ hSubset.
rewrite (@circular_disc_piece_Hausdorff_mass R H hH A hA j z hz) in hMass.
have hDen:0<2*(2* rho j) by lra.
have hDenN:2*(2* rho j)!=0 by rewrite gt_eqF.
have hInv:(0<=((2*(2* rho j))%:E)^-1)%E by rewrite inve_ge0 lee_fin;exact:ltW hDen.
have hQuotient:= lee_wpmul2r hInv hMass.
have hValue:((2* rho j)%:E/((2*(2* rho j))%:E)=((1:R)/2)%:E)%E.
  rewrite inver (gt_eqF hDen) -EFinM;apply:(congr1 (fun x:R=>x%:E)).
  have hRhoN:rho j!=0 by rewrite gt_eqF.
  field.
  by rewrite gt_eqF.
rewrite hValue in hQuotient.
by rewrite /metric_ball_density /measure_restrict euclidean_unit_ball_volume1 expr1.
Qed.

(** Source for [circular_disc_upper_density_at_least_half]:
    the upper density of actual H1 restricted to original
    A is at least one half at every a in A, the lower
    half of the final assertion in 3.3.19, p. 306.
    Actual shrinking level radii are cofinal among positive
    real cutoffs; no chosen radius sequence is assumed. *)
Theorem circular_disc_upper_density_at_least_half (a:E):A a ->
  (((1:R)/2)%:E<=upper_metric_density 1 (measure_restrict mu A) a)%E.
Proof.
move=>ha;rewrite /upper_metric_density /positive_radius_upper_limit.
apply:extended_real_inf_greatest=>b [e [he ->]].
have hHalf:0<e/2 by lra.
have [j hSmall]:= @factorial_disc_radius_small R (@FactorialDiscScales.count R) rho hs (e/2) hHalf.
have hRadius:= hSmall j (leqnn j).
have hPositive:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hs j.
apply:(le_trans (@circular_disc_piece_density_lower a j ha)).
apply:extended_real_sup_upper;exists (2* rho j);split=>//.
apply/andP;split;lra.
Qed.
End Density.
