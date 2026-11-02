(** Federer (1969), 3.2.36, p. 273: convolution with an
    actual point proves invariance under the canonical block embeddings. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  BoundedConvexCartesianIntrinsicVolumes ConvexIntrinsicSingleton ZeroDegreeIntegralGauge
  IntegralGeometricGauge SteinerTubePolynomial FinitePointConvolution CoveringFamilyUP MetricDiameter MetricDiameterMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [first_block_image_cartesian_point]: the canonical
    product-with-a-point image used in the isometry consequence of
    Federer 3.2.36, p. 273. Both block inverse laws give exact
    equality on every source set, without regularity assumptions. *)
Lemma first_block_image_cartesian_point (R:realType) m n
    (A:set (inner_metric_space (@euclidean_inner_productP R m))):
  (@euclidean_first_injection R m n) @` A=
    euclidean_cartesian_set A [set (0%R:inner_metric_space (@euclidean_inner_productP R n))].
Proof.
apply/seteqP; split.
- move=>z [x hx <-].
  change (A ((@euclidean_block_split R m n) ((@euclidean_block_join R m n) (x,0%R))).1 /\
    ((@euclidean_block_split R m n) ((@euclidean_block_join R m n) (x,0%R))).2=0%R).
  by rewrite euclidean_block_joinK; split.
- move=>z [hzA hzB]; exists ((@euclidean_block_split R m n) z).1=>//.
  rewrite /euclidean_first_injection -hzB; exact:euclidean_block_splitK.
Qed.

(** Source for [last_block_image_cartesian_point]: the complementary
    product-with-a-point image used in Federer 3.2.36, p. 273.
    The actual coordinate inverse laws identify the entire image,
    including either zero-dimensional block. *)
Lemma last_block_image_cartesian_point (R:realType) m n
    (B:set (inner_metric_space (@euclidean_inner_productP R n))):
  (@euclidean_last_injection R m n) @` B=
    euclidean_cartesian_set [set (0%R:inner_metric_space (@euclidean_inner_productP R m))] B.
Proof.
apply/seteqP; split.
- move=>z [y hy <-].
  change (((@euclidean_block_split R m n) ((@euclidean_block_join R m n) (0%R,y))).1=0%R /\
    B ((@euclidean_block_split R m n) ((@euclidean_block_join R m n) (0%R,y))).2).
  by rewrite euclidean_block_joinK; split.
- move=>z [hzA hzB]; exists ((@euclidean_block_split R m n) z).2=>//.
  rewrite /euclidean_last_injection -hzA; exact:euclidean_block_splitK.
Qed.

(** Source for [first_canonical_embedding_intrinsic_volume]: the
    product-with-a-point consequence in Federer 3.2.36, p. 273.
    The actual Cartesian convolution and independently proved point
    coefficients leave precisely the original intrinsic volume. Every
    original nonempty bounded convex source and every natural admissible
    degree remain, including zero and degenerate ambient blocks. *)
Theorem first_canonical_embedding_intrinsic_volume (R:realType) m n k
    (hkm:(k<=m)%N) (hkTotal:(k<=m+n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R m))):
  A!=set0 ->is_inner_convex A ->metric_set_bounded A ->
  @integral_geometric_gauge R (m+n) k hkTotal 1 ((@euclidean_first_injection R m n) @` A)=
    @integral_geometric_gauge R m k hkm 1 A.
Proof.
move=>hAN hA hBound.
pose P:set (inner_metric_space (@euclidean_inner_productP R n)):=[set 0%R].
have hPN:P!=set0 by exists 0%R.
have hPC:is_inner_convex P.
  move=>x y -> -> t _ _; by rewrite -scalerDl subrK scale1r.
have hPB:metric_set_bounded P.
  by rewrite /P /metric_set_bounded extended_metric_diameter_singleton; exact:ltry.
pose i:'I_m.+1:=Ordinal (leq_ltn_trans hkm (ltnSn m)).
pose l:'I_(m+n).+1:=Ordinal (leq_ltn_trans hkTotal (ltnSn (m+n))).
have hProduct:=@bounded_convex_cartesian_intrinsic_volumes R m n A P
  hAN hPN hA hPC hBound hPB l.
have hZero:@integral_geometric_gauge R n ord0 (steiner_dimension_guard ord0) 1 P= 1.
  exact:zero_degree_integral_geometric_gauge hPN.
have hPositive (j:'I_n.+1):(0<j)%N ->
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 P=0.
  exact:convex_intrinsic_singleton_positive_degree.
have hSum:=@finite_point_convolution R m n
  (fun i:'I_m.+1=>@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 A)
  (fun j:'I_n.+1=>@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 P) i hZero hPositive.
rewrite first_block_image_cartesian_point.
rewrite (bool_irrelevance hkTotal (steiner_dimension_guard l)) hProduct hSum.
by rewrite (bool_irrelevance (steiner_dimension_guard i) hkm).
Qed.

(** Source for [last_canonical_embedding_intrinsic_volume]: the second
    canonical block embedding has the same original intrinsic volumes,
    Federer 3.2.36, p. 273. Exchange the two finite convolution
    sums, commute each product, and apply the same actual point
    coefficient law. Arbitrary nonmeasurable bounded convex sources
    and all admissible natural degrees are retained. *)
Theorem last_canonical_embedding_intrinsic_volume (R:realType) m n k
    (hkn:(k<=n)%N) (hkTotal:(k<=m+n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n))):
  B!=set0 ->is_inner_convex B ->metric_set_bounded B ->
  @integral_geometric_gauge R (m+n) k hkTotal 1 ((@euclidean_last_injection R m n) @` B)=
    @integral_geometric_gauge R n k hkn 1 B.
Proof.
move=>hBN hB hBound.
pose P:set (inner_metric_space (@euclidean_inner_productP R m)):=[set 0%R].
have hPN:P!=set0 by exists 0%R.
have hPC:is_inner_convex P.
  move=>x y -> -> t _ _; by rewrite -scalerDl subrK scale1r.
have hPB:metric_set_bounded P.
  by rewrite /P /metric_set_bounded extended_metric_diameter_singleton; exact:ltry.
pose j:'I_n.+1:=Ordinal (leq_ltn_trans hkn (ltnSn n)).
pose l:'I_(m+n).+1:=Ordinal (leq_ltn_trans hkTotal (ltnSn (m+n))).
have hProduct:=@bounded_convex_cartesian_intrinsic_volumes R m n P B
  hPN hBN hPC hB hPB hBound l.
have hZero:@integral_geometric_gauge R m ord0 (steiner_dimension_guard ord0) 1 P= 1.
  exact:zero_degree_integral_geometric_gauge hPN.
have hPositive (i:'I_m.+1):(0<i)%N ->
    @integral_geometric_gauge R m i (steiner_dimension_guard i) 1 P=0.
  exact:convex_intrinsic_singleton_positive_degree.
have hSwap:(\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==l)%N)
    @integral_geometric_gauge R m i (steiner_dimension_guard i) 1 P*
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B)=
  \sum_(j:'I_n.+1) \sum_(i:'I_m.+1|(j+i==l)%N)
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B*
    @integral_geometric_gauge R m i (steiner_dimension_guard i) 1 P.
  rewrite (exchange_big_dep predT) //=.
  apply:eq_bigr=>tau _; apply:eq_big.
  - by move=>i; rewrite addnC.
  - by move=>i _; rewrite muleC.
have hSum:=@finite_point_convolution R n m
  (fun j:'I_n.+1=>@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B)
  (fun i:'I_m.+1=>@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 P) j hZero hPositive.
rewrite last_block_image_cartesian_point.
rewrite (bool_irrelevance hkTotal (steiner_dimension_guard l)) hProduct hSwap hSum.
by rewrite (bool_irrelevance (steiner_dimension_guard j) hkn).
Qed.
