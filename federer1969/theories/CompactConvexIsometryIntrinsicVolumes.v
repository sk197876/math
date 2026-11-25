(** Federer (1969), 3.2.36, p. 273: same-ambient
    isometric invariance follows from actual tubes and Steiner coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CompactHausdorffMetric CompactSetDistanceProfile CompactMetricBounded
  MetricIsometricDistanceTransport HausdorffIsometricBijection HausdorffMeasure EuclideanHausdorffLebesgue
  MetricSetDistanceUP ConvexSteinerTubeFormula SteinerTubeScalarPolynomial SteinerTubePolynomial
  ConvexIntrinsicFinitePart SteinerPolynomialCoefficientComparison IntegralGeometricGauge
  EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_isometry_intrinsic_volumes]: the
    same-ambient isometry step in Federer 3.2.36, p. 273.
    Actual distance transport identifies the whole tube images; actual
    Hausdorff invariance and H^n=L^n identify their volumes. The
    proved Steiner formulas and internal finite coefficient comparison
    then identify every original intrinsic volume. Source and target
    compact bodies may be lower-dimensional, including the R^0 atom. *)
Theorem compact_convex_isometry_intrinsic_volumes (R:realType) n
    (A B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (f g:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_inner_convex (val A) ->is_inner_convex (val B) ->
  val B=f @` val A ->cancel f g ->cancel g f ->
  (forall x y,mdist (f x) (f y)=mdist x y) ->
  forall l:'I_n.+1,@integral_geometric_gauge R n l (steiner_dimension_guard l) 1 (val B)=
    @integral_geometric_gauge R n l (steiner_dimension_guard l) 1 (val A).
Proof.
move=>hA hB hImage hGF hFG hMetric.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hDA:=compact_set_distance_profile_specification A.
have hDB:@is_metric_set_distance R X (f @` val A) (compact_set_distance_profile B).
  rewrite -hImage; exact:compact_set_distance_profile_specification.
have hSurj:forall y,exists x,f x=y by move=>y; exists (g y); exact:hFG.
have hVolumes (r:R):
    @euclidean_lebesgue_measure R n [set y|compact_set_distance_profile B y<r]=
    @euclidean_lebesgue_measure R n [set x|compact_set_distance_profile A x<r].
  have hTube:=metric_bijective_isometry_tube_image r hMetric hSurj hDA hDB.
  rewrite -(@euclidean_hausdorff_spherical_lebesgue R n
    [set y|compact_set_distance_profile B y<r]).1 -hTube.
  rewrite (@hausdorff_bijective_isometry_invariance R X X f g hGF hFG hMetric n).
  exact:(@euclidean_hausdorff_spherical_lebesgue R n _).1.
pose c (l:'I_n.+1):R:=fine (@integral_geometric_gauge R n l (steiner_dimension_guard l) 1 (val B)).
pose d (l:'I_n.+1):R:=fine (@integral_geometric_gauge R n l (steiner_dimension_guard l) 1 (val A)).
have hScalar (r:R):0<r ->
    \sum_(l:'I_n.+1) c l*(EuclideanBallVolume.euclidean_unit_ball_volume R (n-l)*r^+(n-l))=
    \sum_(l:'I_n.+1) d l*(EuclideanBallVolume.euclidean_unit_ball_volume R (n-l)*r^+(n-l)).
  move=>hr; have h:=hVolumes r.
  rewrite (@convex_steiner_tube_formula R n (val B) (compact_set_distance_profile B)
    (set_valP B).2 hB (compact_metric_diameter_finite B) (compact_set_distance_profile_specification B) r hr)
    (@convex_steiner_tube_formula R n (val A) (compact_set_distance_profile A)
    (set_valP A).2 hA (compact_metric_diameter_finite A) hDA r hr)
    (@steiner_tube_polynomial_scalar_value R n (val B) r (set_valP B).2 hB (compact_metric_diameter_finite B))
    (@steiner_tube_polynomial_scalar_value R n (val A) r (set_valP A).2 hA (compact_metric_diameter_finite A)) in h.
  exact:EFin_inj h.
have hCoefficients:=steiner_scalar_coefficients_unique hScalar.
move=>l.
rewrite (@convex_intrinsic_finite_part_value R n l (steiner_dimension_guard l) (val B)
  (set_valP B).2 hB (compact_metric_diameter_finite B))
  (@convex_intrinsic_finite_part_value R n l (steiner_dimension_guard l) (val A)
  (set_valP A).2 hA (compact_metric_diameter_finite A)).
change ((c l)%:E=(d l)%:E).
by rewrite (hCoefficients l).
Qed.
