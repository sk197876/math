(** Federer (1969), 3.2.36, p. 273: substitute the actual
    distance-level and tube polynomials into the product coarea integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CompactHausdorffMetric CompactSetDistanceProfile CompactMetricBounded SteinerTubePolynomial
  SteinerDistanceLevelPolynomial ConvexSteinerTubeFormula ConvexIntrinsicVolumeIntegrals
  IntegralGeometricGauge EuclideanBallVolume EuclideanLebesgueDimensions HausdorffMeasure
  RadialSectionWeightedIntegral LebesgueScalarMeasure RealOpenIntervals MetricSetDistanceUP
  PartialFunctionBasic MeasureSubsetIntegral SubsetFiniteNonnegativeIntegral SubsetIntegralTotalAgreement
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_product_radial_polynomial_integral]: the finite
    radius integration in the second and third displays of Federer
    3.2.36, p. 273. Both actual factor polynomials are substituted;
    each nonnegative intrinsic-volume weight multiplies its proved radial
    integral and the finite sums are interchanged using actual integral
    laws. The coefficient is alpha(xi+eta), including eta=0; no
    convolution identity is assumed. All compact nonempty convex factors,
    including lower-dimensional factors and n=0, are retained. *)
Theorem convex_product_radial_polynomial_integral (R:realType) k n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R k.+1)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  is_inner_convex (val A) ->is_inner_convex (val B) ->(0<r)%R ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (partial_function_total (fun s:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R k.+1)) k
        [set x|compact_set_distance_profile A x=s]*
      @euclidean_lebesgue_measure R n
        [set y|(compact_set_distance_profile B y<Num.sqrt (r^+2-s^+2))%R]
        :extended_real_line R)))
    (\sum_(i:'I_k.+1) \sum_(j:'I_n.+1)
      (@integral_geometric_gauge R k.+1 i
        (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 (val A)*
       @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (val B))*
      (euclidean_unit_ball_volume R ((k.+1-i)+(n-j))*r^+((k.+1-i)+(n-j)))%R%:E).
Proof.
move=>hA hB hr.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
pose I:=real_open_interval 0 r.
pose G (i:'I_k.+1): \bar R:=@integral_geometric_gauge R k.+1 i
  (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 (val A).
pose H (j:'I_n.+1): \bar R:=@integral_geometric_gauge R n j
  (steiner_dimension_guard j) 1 (val B).
pose v (i:'I_k.+1) (j:'I_n.+1) (s:R):R:=
  ((k.+1-i)%:R*euclidean_unit_ball_volume R (k.+1-i)*
    euclidean_unit_ball_volume R (n-j)*s^+((k.+1-i)-1)*Num.sqrt (r^+2-s^+2)^+(n-j))%R.
pose u (i:'I_k.+1) (j:'I_n.+1) (s:R):extended_real_line R:=G i*H j*(v i j s)%:E.
pose a (i:'I_k.+1) (j:'I_n.+1): \bar R:=G i*H j*
  (euclidean_unit_ball_volume R ((k.+1-i)+(n-j))*r^+((k.+1-i)+(n-j)))%R%:E.
have hG i:0<=G i.
  exact:(@convex_intrinsic_volume_nonnegative_finite R k.+1 i
    (leq_trans (steiner_dimension_guard i) (leqnSn k)) 1 (val A)
    (set_valP A).2 hA (compact_metric_diameter_finite A) (lexx 1)).1.
have hH j:0<=H j.
  exact:(@convex_intrinsic_volume_nonnegative_finite R n j (steiner_dimension_guard j) 1 (val B)
    (set_valP B).2 hB (compact_metric_diameter_finite B) (lexx 1)).1.
have hV i j s:I s ->(0<=v i j s)%R.
  move=>[hs _]; rewrite /v; apply:mulr_ge0; last by apply:exprn_ge0; exact:sqrtr_ge0.
  apply:mulr_ge0; last by apply:exprn_ge0; exact:ltW hs.
  apply:mulr_ge0; last exact:ltW (euclidean_unit_ball_volumeE R (n-j)).2.
  apply:mulr_ge0; [exact:ler0n|exact:ltW (euclidean_unit_ball_volumeE R (k.+1-i)).2].
have hU i j s:I s ->0<=u i j s.
  move=>hs; apply:mule_ge0; first exact:mule_ge0 (hG i) (hH j).
  rewrite lee_fin; exact:hV i j s hs.
have hIntegral i j:is_measure_subset_integral mu I (partial_function_total (u i j)) (a i j).
  have hXi:(0<k.+1-i)%N by rewrite subn_gt0; exact:ltn_ord i.
  exact:(@radial_section_weighted_integral R (k.+1-i) (n-j) r (G i*H j) hXi hr
    (mule_ge0 (hG i) (hH j))).
have hInner i:=@subset_finite_nonnegative_integral R R [the finType of 'I_n.+1] mu hm I
  (u i) (a i) (hU i) (hIntegral i).
have hInnerPositive i s:I s ->0<= \sum_j u i j s.
  move=>hs; apply:sume_ge0=>j _; exact:hU i j s hs.
have hSum:=@subset_finite_nonnegative_integral R R [the finType of 'I_k.+1] mu hm I
  (fun i s=>(\sum_j u i j s:extended_real_line R)) (fun i=>\sum_j a i j)
  hInnerPositive hInner.
apply:(@subset_integral_total_agreement R R mu I
  (fun s:R=>(\sum_i \sum_j u i j s:extended_real_line R))
  (fun s:R=>(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k
    [set x|compact_set_distance_profile A x=s]*@euclidean_lebesgue_measure R n
    [set y|(compact_set_distance_profile B y<Num.sqrt (r^+2-s^+2))%R]:extended_real_line R))
  _ _).1 hSum.
move=>s [hs hsr]; symmetry.
have hRoot:(0<Num.sqrt (r^+2-s^+2))%R.
  by rewrite sqrtr_gt0 subr_gt0 (ltr_sqr (ltW hs) (ltW hr)).
rewrite (@convex_distance_level_polynomial R k (val A) (compact_set_distance_profile A) s
  (set_valP A).2 hA (compact_metric_diameter_finite A)
  (compact_set_distance_profile_specification A) hs).
rewrite (@convex_steiner_tube_formula R n (val B) (compact_set_distance_profile B)
  (set_valP B).2 hB (compact_metric_diameter_finite B)
  (compact_set_distance_profile_specification B) _ hRoot) /steiner_tube_polynomial.
have hLevelPositive i:0<=G i*((k.+1-i)%:R*euclidean_unit_ball_volume R (k.+1-i)*s^+(k-i))%R%:E.
  apply:mule_ge0; first exact:hG.
  rewrite lee_fin; apply:mulr_ge0; last by apply:exprn_ge0; exact:ltW hs.
  apply:mulr_ge0; [exact:ler0n|exact:ltW (euclidean_unit_ball_volumeE R (k.+1-i)).2].
have hTubePositive j:0<=H j*(euclidean_unit_ball_volume R (n-j)*Num.sqrt (r^+2-s^+2)^+(n-j))%R%:E.
  apply:mule_ge0; first exact:hH.
  rewrite lee_fin; apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R (n-j)).2.
  apply:exprn_ge0; exact:sqrtr_ge0.
rewrite ge0_sume_distrl; last by move=>i _; exact:hLevelPositive.
apply:eq_bigr=>i _.
rewrite ge0_sume_distrr; last by move=>j _; exact:hTubePositive.
apply:eq_bigr=>j _.
have hDegree:(k.+1-i-1)%N=(k-i)%N by rewrite subSn ?subn1 //; exact:steiner_dimension_guard.
have hProduct (aa cc: \bar R) (bb dd:R):(aa*bb%:E)*(cc*dd%:E)=(aa*cc)*(bb*dd)%R%:E.
  by rewrite EFinM !muleA [aa*bb%:E*cc]muleAC.
rewrite hProduct /u /v hDegree.
congr ((G i*H j)*_%:E); ring.
Qed.
