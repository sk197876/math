(** Federer (1969), 3.2.45, p. 280: the original cube
    product bound follows from the already proved Cartesian intrinsic
    convolution, exact cube coefficients, and the degree-drop estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry CoordinateCubeIntrinsicVolumes
  EuclideanCartesianMap BoundedConvexCartesianIntrinsicVolumes IntegralGeometricGauge
  CompactSetDistanceProfile CompactMetricBounded
  ConvexIntrinsicFinitePart ConvexIntrinsicVolumeIntegrals SteinerTubePolynomial
  MetricDiameterUP MetricDiameter ExtendedSupremumPowers ExtendedRealOrderTopology
  ConvexIntrinsicUniformDegreeBound FiniteBinomialConvolutionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_cube_product_intrinsic_bound]: the cube-product
    estimate in Federer 3.2.45, p. 280, written as
    zeta^(m+k)(P times Q) <= zeta^k(Q) (s+M diam Q)^m.
    The common finite M depends only on the ambient second-factor
    dimension and k. Actual boundedness justifies the finite diameter;
    no measurability, positive volume or positive side is added. *)
Theorem convex_cube_product_intrinsic_bound (R : realType) n k (hKN : (k <= n)%N) :
  exists M : R, (1 < M)%R /\
    forall m (a : R_n R m) (s : R)
      (P : set (inner_metric_space (@euclidean_inner_productP R m)))
      (Q : set (inner_metric_space (@euclidean_inner_productP R n))),
      is_euclidean_coordinate_cube a s P ->
      Q !=set0 -> is_inner_convex Q -> metric_set_bounded Q ->
      @integral_geometric_gauge R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
          (euclidean_cartesian_set P Q) <=
        @integral_geometric_gauge R n k hKN 1 Q *
          ((s + M * fine (extended_metric_diameter Q))^+m)%R%:E.
Proof.
have [M [hM hDegree]] := @convex_intrinsic_uniform_degree_bound R n k hKN.
exists M; split=> // m a s P Q hP hNonempty hConvex hBound.
pose b (j : 'I_n.+1) : R := fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q).
pose G : R := fine (@integral_geometric_gauge R n k hKN 1 Q).
pose d : R := fine (extended_metric_diameter Q).
have hDiameter : extended_metric_diameter Q = d%:E.
  symmetry; apply: fineK.
  rewrite (ge0_fin_numE (metric_diameter_nonnegative (extended_metric_diameter_specification Q))).
  exact hBound.
have hd : (0 <= d)%R.
  have h := metric_diameter_nonnegative (extended_metric_diameter_specification Q).
  by rewrite hDiameter lee_fin in h.
have hGValue := @convex_intrinsic_finite_part_value R n k hKN Q hNonempty hConvex hBound.
have hG : (0 <= G)%R.
  have h := (@convex_intrinsic_volume_nonnegative_finite R n k hKN 1 Q
    hNonempty hConvex hBound (lexx 1)).1.
  by rewrite hGValue lee_fin in h.
have hBValue (j : 'I_n.+1) :
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 Q = (b j)%:E.
  exact: convex_intrinsic_finite_part_value hNonempty hConvex hBound.
have hTransport (j1 j2 : nat) (h1 : (j1 <= n)%N) (h2 : (j2 <= n)%N) :
    j1 = j2 -> @integral_geometric_gauge R n j1 h1 1 Q =
      @integral_geometric_gauge R n j2 h2 1 Q.
  move=> hEqual; subst j2.
  by have -> : h1 = h2 := Prop_irrelevance _ _.
have hB (j : 'I_n.+1) (hKJ : (k <= j)%N) : (b j <= G * (M * d)^+(j-k))%R.
  have hIndex : (j-k+k = j)%N := subnK hKJ.
  have hJN : (j-k+k <= n)%N by rewrite hIndex; have := ltn_ord j; rewrite ltnS.
  have h := hDegree (j-k)%N hJN Q hNonempty hConvex hBound.
  rewrite (hTransport _ _ hJN (steiner_dimension_guard j) hIndex)
    hBValue hGValue hDiameter -EFin_expe -!EFinM lee_fin in h.
  rewrite exprMn mulrA [(G * _)%R]mulrC.
  exact h.
pose l : 'I_(m+n).+1 := Ordinal (leq_ltn_trans (leq_add (leqnn m) hKN) (ltnSn (m+n))).
have hConvolution := @bounded_convex_cartesian_intrinsic_volumes R m n P Q
  (coordinate_cube_nonempty hP) hNonempty (coordinate_cube_convex hP) hConvex
  (compact_metric_diameter_finite (exist _ P (mem_set (conj (coordinate_cube_compact hP)
    (coordinate_cube_nonempty hP))))) hBound l.
have hLGuard : steiner_dimension_guard l = leq_add (leqnn m) hKN := Prop_irrelevance _ _.
rewrite /l /= hLGuard in hConvolution.
have hProduct :
    @integral_geometric_gauge R (m+n) (m+k) (leq_add (leqnn m) hKN) 1
      (euclidean_cartesian_set P Q) =
    (\sum_(i : 'I_m.+1) \sum_(j : 'I_n.+1 | (i+j == m+k)%N)
      ('C(m,i)%:R * s^+i) * b j)%:E.
  rewrite hConvolution -sumEFin.
  apply: eq_bigr=> i _; rewrite -sumEFin.
  apply: eq_bigr=> j _.
  by rewrite (coordinate_cube_intrinsic_volume hP i) hBValue -EFinM.
rewrite hProduct hGValue -EFinM lee_fin.
exact: finite_binomial_convolution_bound hG (mulr_ge0 (ltW (lt_trans ltr01 hM)) hd) hP.1 hB.
Qed.
