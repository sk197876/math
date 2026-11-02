(** Federer (1969), 3.2.26(2), p. 261: each
    compact chart point has arbitrarily small translated
    convex covers with cost at most (1+delta) alpha(m) r^m.
    Every differential and all inverse estimates are obtained
    from the chart laws, rather than assumed as a field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric HilbertFormCompactness InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorNorm
  AssociatedSubspace NormDifferentialUP LinearEmbeddingContinuity RectifiableCompactChartsUP
  EuclideanDifferentialOrientation EuclideanDifferentialOrientationContinuity SimpleUnitPartialExteriorNorm
  OrthogonalDiscConvexNeighbourhood DifferentiableChartDiscNeighbourhood EuclideanSimilarityCoverGeometry
  IntegralGeometricSimilarityGauge IntegralGeometricGauge EuclideanBallVolume InnerConvex MetricClosedBalls
  MetricDiameter BorelClosedProjection TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_compact_chart_local_convex_covers]: the
    thin-cover construction in 3.2.26(2), p. 261.
    The displacement is x-w, as corrected by the erratum
    p. 5, book p. 261 line 29. Use a near-optimal
    open convex unit-disc neighbourhood, then translate it
    to the actual chart point and scale by r. Its
    diameter is at most 3r, which suffices for the
    same arbitrarily small cutoff argument. *)
Theorem uniform_compact_chart_local_convex_covers (R:realType) m n
    (hmn:(m<=n)%N) (lambda:R) (K:set (R_n R m))
    (psi:R_n R m->R_n R n) (w:R_n R n) (t: \bar R) (d:R):
  (0<lambda)%R ->is_uniform_compact_rectifiable_chart lambda K psi ->
  (psi @` K) w ->1<=t ->(0<d)%R ->
  exists s:R,(0<s)%R /\forall r:R,(0<r<s)%R ->
    exists U:set (inner_metric_space (@euclidean_inner_productP R n)),
      open U /\@is_inner_convex R (R_n R n) U /\
      (psi @` K) `&` @metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R n)) w r `<=` U /\
      extended_metric_diameter U<=(r*3)%R%:E /\
      @integral_geometric_gauge R n m hmn t U<=
        ((1+d)*euclidean_unit_ball_volume R m*r^+m)%R%:E.
Proof.
move=>hLambda hChart [a ha hPsi] ht hd.
have [D [hD hBounds]]:=@rectifiable_chart_differential_bounds R m n lambda K psi hChart a ha.
have hInjective:injective D.
  apply:(norm_linear_lower_bound_injective
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n))).
  exists (lambda^-1)%R; split; first by rewrite invr_gt0.
  move=>v; exact:(hBounds v).1.
pose xi:=euclidean_differential_orientation D.
have [hSimple hUnit]:=euclidean_differential_orientation_unit_simple hInjective.
change (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) xi= 1%R) in hUnit.
have [f [eta [hF [hRange [hMap hEta]]]]]:=simple_unit_orthogonal_frame_lift hSimple hUnit.
have hAssociated:=euclidean_differential_orientation_associated hInjective.
have hRangeD x:exists u,f u=D x.
  apply:(hRange (D x)).2.
  change (([set v|FedererSimple.T xi v]) (D x)).
  rewrite hAssociated; exists x; first exact I; reflexivity.
have [V [hOpen [hConvex [hDisc [hDiam hGauge]]]]]:=
  @orthogonal_disc_near_optimal_convex_neighbourhood R m n hmn f t d hF ht hd.
have hInverse b:K b ->(inner_norm (@euclidean_inner_productP R m) (b-a)<=
    lambda*inner_norm (@euclidean_inner_productP R n) (psi b-psi a))%R.
  move=>hb; exact:(@rectifiable_chart_inverse_bound R m n lambda K psi hChart b a hb ha).
have [s [hs hContain]]:=@differentiable_chart_unit_disc_neighbourhood R m n K psi a D f lambda V
  hLambda hInverse hD hF hRangeD hOpen hDisc.
exists s; split; first exact hs; move=>r hRadius.
have hr:(0<r)%R:=(andP hRadius).1.
have hNonzero:r!=0%R by rewrite gt_eqF.
pose U:=(fun x=>(w+r*:x)%R) @` V.
exists U; split; first exact:(euclidean_positive_similarity_open hr hOpen).
split; first exact:(@euclidean_similarity_convex R n V w r hConvex).
split.
- move=>z [[b hb hPsiB] hBall].
  have hDistance:(inner_norm (@euclidean_inner_productP R n) (psi b-psi a)<=r)%R.
    rewrite -hPsi -hPsiB in hBall.
    move:hBall; rewrite /metric_closed_ball /= inner_metric_distanceE
      -[(psi a-psi b)%R]opprB inner_normN; by [].
  have hNormalized:=hContain r hRadius b hb hDistance.
  exists ((r^-1*:(psi b-psi a))%R); first exact hNormalized.
  by rewrite -hPsiB -hPsi scalerA (mulfV hNonzero) scale1r addrC subrK.
- split.
  + exact:(@euclidean_positive_similarity_diameter_bound R n V w r 3 (ltW hr)
      (ler0n _ _) hDiam).
  + rewrite /U (@integral_geometric_positive_similarity_gauge R n m hmn t V w r ht
      (metric_borel_suslin (open_borel_set hOpen)) hr).
    have hPower:(0<=(r^+m))%R:=exprn_ge0 m (ltW hr).
    have hBound:=lee_wpmul2l (lee_tofin hPower) hGauge.
    by rewrite -EFinM mulrC in hBound.
Qed.
