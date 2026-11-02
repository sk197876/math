(** Federer (1969), 3.2.36, p. 273: the normalized actual
    product-tube polynomial, prior to comparison of its coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates EuclideanCartesianMap CompactHausdorffMetric CompactSetDistanceProfile CompactMetricBounded
  EuclideanProductTubeSplitting EuclideanProductRadialCoarea ConvexProductRadialPolynomialIntegral
  SteinerTubePolynomial ConvexSteinerTubeFormula ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge
  FullDimensionIntegralGauge ZeroDegreeIntegralGauge EuclideanBallVolume EuclideanLebesgueDimensions
  MetricSetDistanceUP MeasureUP MeasureBasic MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_cartesian_tube_polynomial]: the finite expression
    in the third display of Federer 3.2.36, p. 273, after
    the radial coefficients are proved to be alpha(xi+eta).
    It uses only the original actual normalized intrinsic volumes,
    with all endpoint indices and natural coordinate blocks retained. *)
Definition convex_cartesian_tube_polynomial (R:realType) m n
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R): \bar R:=
  \sum_(i:'I_m.+1) \sum_(j:'I_n.+1)
    (@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 A*
     @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B)*
    (euclidean_unit_ball_volume R ((m-i)+(n-j))*r^+((m-i)+(n-j)))%R%:E.

(** Source for [convex_cartesian_tube_polynomial_positive_first]: the
    entire actual product-tube volume calculation in Federer 3.2.36,
    p. 273, for a positive first coordinate block. The zero-distance
    rectangle and proved finite radial integral combine to give the
    full normalized polynomial, including the top first-factor index.
    No product convolution or positive factor mass is assumed. *)
Theorem convex_cartesian_tube_polynomial_positive_first (R:realType) k n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R k.+1)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (k.+1+n))->R) (r:R):
  is_inner_convex (val A) ->is_inner_convex (val B) ->
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (k.+1+n)))
    (euclidean_cartesian_set (val A) (val B)) d ->(0<r)%R ->
  @euclidean_lebesgue_measure R (k.+1+n) [set z|(d z<r)%R]=
    convex_cartesian_tube_polynomial (val A) (val B) r.
Proof.
move=>hA hB hD hr.
have hCoarea:=@euclidean_product_radial_coarea R k n A B d r hA hD.
have hIntegrated:=@convex_product_radial_polynomial_integral R k n A B r hA hB hr.
have hPositive:=measure_integral_unique hCoarea hIntegrated.
rewrite (@euclidean_product_tube_volume_splitting R k.+1 n A B d r hD hr) hPositive.
rewrite /convex_cartesian_tube_polynomial [RHS]big_ord_recr.
have hLast: \sum_(j:'I_n.+1)
    (@integral_geometric_gauge R k.+1 k.+1 (steiner_dimension_guard ord_max) 1 (val A)*
      @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (val B))*
    (euclidean_unit_ball_volume R ((k.+1-k.+1)+(n-j))*r^+((k.+1-k.+1)+(n-j)))%R%:E=
    @euclidean_lebesgue_measure R k.+1 (val A)*
      @euclidean_lebesgue_measure R n [set y|(compact_set_distance_profile B y<r)%R].
  rewrite subnn ?add0n (@equal_dimension_integral_geometric_gauge R k.+1 _ 1 (val A) (lexx 1)).
  rewrite (@convex_steiner_tube_formula R n (val B) (compact_set_distance_profile B)
    (set_valP B).2 hB (compact_metric_diameter_finite B)
    (compact_set_distance_profile_specification B) r hr) /steiner_tube_polynomial.
  rewrite ge0_sume_distrr; last first.
  - move=>j _; apply:mule_ge0.
    + exact:(@convex_intrinsic_volume_nonnegative_finite R n j (steiner_dimension_guard j) 1 (val B)
        (set_valP B).2 hB (compact_metric_diameter_finite B) (lexx 1)).1.
    + rewrite lee_fin; apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R (n-j)).2.
      apply:exprn_ge0; exact:ltW hr.
  apply:eq_bigr=>j _.
  rewrite !add0n !muleA.
  by [].
rewrite hLast addeC.
congr (_+_); apply:eq_bigr=>i _; apply:eq_bigr=>j _.
by rewrite (bool_irrelevance (leq_trans (steiner_dimension_guard i) (leqnSn k))
  (steiner_dimension_guard (widen_ord (leqnSn k.+1) i))).
Qed.

(** Source for [convex_cartesian_tube_polynomial_zero_first]: the empty
    first-block boundary of the same actual volume calculation in
    Federer 3.2.36, p. 273. A nonempty subset of R^0 is
    the whole one-point space, so its distance is zero and its volume
    and zeroth intrinsic volume are one. The positive-distance piece
    is empty; every second coordinate dimension is retained. *)
Theorem convex_cartesian_tube_polynomial_zero_first (R:realType) n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R 0)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (0+n))->R) (r:R):
  is_inner_convex (val B) ->
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (0+n)))
    (euclidean_cartesian_set (val A) (val B)) d ->(0<r)%R ->
  @euclidean_lebesgue_measure R (0+n) [set z|(d z<r)%R]=
    convex_cartesian_tube_polynomial (val A) (val B) r.
Proof.
move=>hB hD hr.
have [a ha]:=(set_valP A).2.
have hMember x:val A x.
  have hEqual:x=a by rewrite (coordinate_zero x) (coordinate_zero a).
  by rewrite hEqual.
have hProfile x:compact_set_distance_profile A x=(0%R:R).
  exact:(compact_set_distance_profile_zero A x).2 (hMember x).
have hEmpty:([set z:inner_metric_space (@euclidean_inner_productP R (0+n))|
    (0<compact_set_distance_profile A (euclidean_block_split z).1<r)%R] `&` [set z|(d z<r)%R])=set0.
  apply/seteqP; split; last by move=>z [].
  move=>z [/andP[hz _] _]; by rewrite hProfile ltxx in hz.
have hVolume:@euclidean_lebesgue_measure R 0 (val A)= 1.
  rewrite -(@equal_dimension_integral_geometric_gauge R 0 (leqnn 0) 1 (val A) (lexx 1)).
  exact:zero_degree_integral_geometric_gauge (set_valP A).2.
rewrite (@euclidean_product_tube_volume_splitting R 0 n A B d r hD hr) hEmpty
  (measure_empty (euclidean_lebesgue_is_measure R (0+n))) hVolume mul1e adde0.
rewrite /convex_cartesian_tube_polynomial big_ord_recr big_ord0 ?add0r.
rewrite (@zero_degree_integral_geometric_gauge R 0 _ (val A) (set_valP A).2).
have hTube:=@convex_steiner_tube_formula R n (val B) (compact_set_distance_profile B)
  (set_valP B).2 hB (compact_metric_diameter_finite B) (compact_set_distance_profile_specification B) r hr.
rewrite hTube /steiner_tube_polynomial.
change ((\sum_(j:'I_n.+1) @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (val B)*
  (euclidean_unit_ball_volume R (n-j)*r^+(n-j))%R%:E)=
  (0+\sum_(j:'I_n.+1) (1* @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (val B))*
  (euclidean_unit_ball_volume R (n-j)*r^+(n-j))%R%:E))%E.
rewrite add0e; apply:eq_bigr=>j _; by rewrite mul1e.
Qed.

(** Source for [convex_cartesian_tube_volume_polynomial]: the full
    third displayed equality in Federer 3.2.36, p. 273, before
    comparison with the product body's own Steiner coefficients. Both
    original compact convex factors may have zero volume, and all
    natural coordinate blocks, including zero, are covered. *)
Theorem convex_cartesian_tube_volume_polynomial (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (m+n))->R) (r:R):
  is_inner_convex (val A) ->is_inner_convex (val B) ->
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (m+n)))
    (euclidean_cartesian_set (val A) (val B)) d ->(0<r)%R ->
  @euclidean_lebesgue_measure R (m+n) [set z|(d z<r)%R]=
    convex_cartesian_tube_polynomial (val A) (val B) r.
Proof.
case:m A d=>[A d _|k A d hA].
- exact:convex_cartesian_tube_polynomial_zero_first.
- exact:convex_cartesian_tube_polynomial_positive_first hA.
Qed.
