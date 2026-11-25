(** Supporting Federer (1969), 3.2.45, p. 280:
    finite equal cube subdivision at a prescribed Q_1 cutoff.
    *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry CoordinateCubeSubdivision
  EqualCoordinateCubeGridUP EqualCoordinateCubeGridLaws EuclideanCartesianMap
  EuclideanBlockCoordinates EuclideanSquaredProduct EuclideanRectangleConvex SquaredProductDiameter
  MetricProductRectangles MetricDiameterUP MetricDiameter CoveringFamilyUP
  ConvexCubeProductIntrinsicBound ConvexIntrinsicFinitePart
  IntegralGeometricGauge ProjectionMeasureUP TopologicalBorel BorelClosedProjection
  MetricScaleEnvelopeUP MetricScaleCutoffCost MetricScaleWeightedBound CaratheodoryBorelRegular
  FiniteCoverMeasureBounds MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_cube_subdivision_cutoff_bound]: expanded
    finite-cover step in Federer 3.2.45, p. 280. One
    M>1 works in all first-factor dimensions. Subdivide
    an actual side-s coordinate cube into v^m cubes and
    retain the original Q_1 cutoff. The resulting bound is
    zeta^k(Q) (s+v M d)^m when diam Q<=d. The
    source generator Q is nonempty, bounded, closed and
    convex; these conditions are discharged for the actual
    closed-convex construction in the later covering passage.
    This is a local covering estimate, not the final product theorem. *)
Theorem convex_cube_subdivision_cutoff_bound (R : realType) n k (hKN : (k <= n)%N) :
  exists M : R, (1 < M)%R /\
  forall m v (a : R_n R m) (s d : R)
    (P : set (inner_metric_space (@euclidean_inner_productP R m)))
    (Q : set (inner_metric_space (@euclidean_inner_productP R n)))
    (delta : \bar R)
    (xi : set (inner_metric_space (@euclidean_inner_productP R (m+n))) -> \bar R),
    (0 < v)%N -> is_euclidean_coordinate_cube a s P ->
    Q !=set0 -> closed Q -> is_inner_convex Q -> (0 <= d)%R ->
    extended_metric_diameter Q <= d%:E ->
    ((m%:R*(s/v%:R)+d)%R)%:E <= delta ->
    is_metric_scale_envelope
      (fun j : closed_convex_euclidean_sets R (m+n) => val j)
      (fun j => @integral_geometric_gauge R (m+n) (m+k) (leq_add (leqnn m) hKN) 1 (val j))
      delta xi ->
    xi (euclidean_cartesian_set P Q) <=
      @integral_geometric_gauge R n k hKN 1 Q * ((s+v%:R*M*d)^+m)%R%:E.
Proof.
have [M [hM hIntrinsic]] := @convex_cube_product_intrinsic_bound R n k hKN.
exists M; split=> // m v a s d P Q delta xi hV hP hNonempty hClosed hConvex hD hDiameter hCutoff hXi.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose Z := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose J := closed_convex_euclidean_sets R (m+n).
pose c := fun j : J => @integral_geometric_gauge R (m+n) (m+k) (leq_add (leqnn m) hKN) 1 (val j).
pose h : R := (s/v%:R)%R.
have hVR : (0 < v%:R :> R)%R by rewrite ltr0n.
have hVNe : (v%:R : R) != 0%R := lt0r_neq0 hVR.
have hH : (0 <= h)%R by rewrite /h divr_ge0 //; exact hP.1.
have hWidth : (v%:R*h = s)%R by rewrite /h mulrC divfK.
have hPGrid : is_euclidean_coordinate_cube a (v%:R*h)%R P by rewrite hWidth.
have [T [hT hUnion]] := @coordinate_cube_subdivision_exists R m v a h P hV hH hPGrid.
pose I := coordinate_cube_grid_indices m v.
pose S (j : I) : set Z := euclidean_cartesian_set (T j) Q.
have hCostNonnegative (j : J) : 0 <= c j.
  apply: integral_geometric_gauge_nonnegative; first exact: lexx.
  apply: metric_borel_suslin; exact: closed_borel_set (set_valP j).1.
have hXiMeasure : is_measure xi := metric_scale_envelope_is_measure hXi hCostNonnegative.
have hBound : metric_set_bounded Q := le_lt_trans hDiameter (ltry d).
pose G : R := fine (@integral_geometric_gauge R n k hKN 1 Q).
have hGValue : @integral_geometric_gauge R n k hKN 1 Q = G%:E.
  exact: convex_intrinsic_finite_part_value hNonempty hConvex hBound.
have hG : (0 <= G)%R.
  have hGaugeNonnegative := @integral_geometric_gauge_nonnegative R n k hKN 1 (lexx 1) Q
    (metric_borel_suslin (closed_borel_set hClosed)).
  by rewrite hGValue lee_fin in hGaugeNonnegative.
have hFineDiameter : extended_metric_diameter Q = (fine (extended_metric_diameter Q))%:E.
  symmetry; apply: fineK.
  rewrite (ge0_fin_numE (metric_diameter_nonnegative (extended_metric_diameter_specification Q))).
  exact hBound.
have hFineD : (fine (extended_metric_diameter Q) <= d)%R.
  by move: hDiameter; rewrite hFineDiameter lee_fin.
have hFineD0 : (0 <= fine (extended_metric_diameter Q))%R.
  have hDiameterNonnegative := metric_diameter_nonnegative (extended_metric_diameter_specification Q).
  by rewrite hFineDiameter lee_fin in hDiameterNonnegative.
have hMPositive : (0 < M)%R := lt_trans ltr01 hM.
have hCell j := @equal_coordinate_grid_cell_cube R m v a h T hT j.
have hCellDiameter (j : I) : extended_metric_diameter (T j) <= ((m%:R*h)%R)%:E.
  apply: (metric_diameter_least (extended_metric_diameter_specification _)).
  - rewrite lee_fin; exact: mulr_ge0 (ler0n R m) hH.
  - move=> x y hx hy; rewrite lee_fin.
    exact (@coordinate_cube_distance_bound R m
      ([ffun i => (a i+(j i)%:R*h)%R] : R_n R m) h (T j) (hCell j) x y hx hy).
have hProductDiameter (j : I) : @extended_metric_diameter R [the metricType R of Z]
    (S j) <= ((m%:R*h+d)%R)%:E.
  exact: (@squared_product_rectangle_diameter_bound R
    [the metricType R of Z] [the metricType R of X] [the metricType R of Y]
    (fun x y => euclidean_block_join (x,y))
    (fun z => (euclidean_block_split z).1) (fun z => (euclidean_block_split z).2)
    (@euclidean_blocks_are_squared_metric_product R m n) (T j) Q
    (m%:R*h)%R d (m%:R*h+d)%R
    (mulr_ge0 (ler0n R m) hH) hD (addr_ge0 (mulr_ge0 (ler0n R m) hH) hD)
    ltac:(have hA := mulr_ge0 (ler0n R m) hH; nra) (hCellDiameter j) hDiameter).
have hCellCost (j : I) : xi (S j) <= (G*(h+M*d)^+m)%R%:E.
  have hCellClosed : closed (T j).
    exact: compact_closed (@metric_hausdorff R [the metricType R of X]) (coordinate_cube_compact (hCell j)).
  have hProductClosed : closed (S j) := euclidean_rectangle_closed hCellClosed hClosed.
  have hProductConvex : is_inner_convex (S j) := euclidean_rectangle_convex
    (coordinate_cube_convex (hCell j)) hConvex.
  pose q : J := exist _ (S j) (mem_set (conj hProductClosed hProductConvex)).
  have hPieceCutoff : extended_metric_diameter (val q) <= delta := le_trans (hProductDiameter j) hCutoff.
  have hGenerator := @metric_scale_generator_bound R [the metricType R of Z] J
    (fun z => val z) c delta xi q hXi (hCostNonnegative q) hPieceCutoff.
  have hVolume := hIntrinsic m _ h (T j) Q (hCell j) hNonempty hConvex hBound.
  have hPower : ((h+M*fine (extended_metric_diameter Q))^+m <= (h+M*d)^+m)%R.
    apply: lerXn2r.
    - exact: addr_ge0 hH (mulr_ge0 (ltW hMPositive) hFineD0).
    - exact: addr_ge0 hH (mulr_ge0 (ltW hMPositive) hD).
    - have hScaledDiameter := ler_wpM2l (ltW hMPositive) hFineD.
      exact (lerD (lexx h) hScaledDiameter).
  have hScaled := ler_wpM2l hG hPower.
  rewrite hGValue -EFinM in hVolume.
  exact (le_trans hGenerator (le_trans hVolume (lee_tofin hScaled))).
have hCover : euclidean_cartesian_set P Q `<=` \bigcup_(j in @setT I) S j.
  move=> z [hPz hQz].
  rewrite hUnion in hPz; have [j _ hJ] := hPz.
  exists j=> //; by split.
have hCoverBound := @measure_finite_indexed_cover R [the choiceType of Z] I xi hXiMeasure
  (euclidean_cartesian_set P Q) S hCover.
have hCard : #|I| = (v^m)%N.
  change (#|{ffun 'I_m -> 'I_v}| = (v^m)%N).
  by rewrite card_ffun !card_ord.
have hSum : (\sum_(j : I) (G*(h+M*d)^+m)%R%:E) =
    (G*(s+v%:R*M*d)^+m)%R%:E.
  rewrite sumEFin.
  congr (_%:E).
  rewrite sumr_const.
  change ((G*(h+M*d)^+m) *+ #|I| = G*(s+v%:R*M*d)^+m)%R.
  rewrite -(mulr_natl (G*(h+M*d)^+m)%R #|I|) hCard natrX mulrCA -exprMn.
  have hEqual : (v%:R*(h+M*d) = s+v%:R*M*d)%R.
    by rewrite mulrDr hWidth mulrA.
  by rewrite hEqual.
rewrite hGValue -EFinM -hSum.
apply: le_trans hCoverBound _; apply: lee_sum=> j _; exact: hCellCost.
Qed.
