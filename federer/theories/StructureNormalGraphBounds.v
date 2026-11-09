(** Federer (1969), 3.3.5, p. 292: the actual normal-coordinate
    inverse has the sharp transverse Lipschitz bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanProjectionSpace EuclideanBlockLinearMaps EuclideanRightBlockProjection
  OrthogonalProjectionChartUP StructureConeAvoidance StructureBlockCone
  SignedSquareRootSealed SignedSquareRootLaws MetricDiameter LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projection_chart_squared_norm]: the
    original identity |x| squared=|p(x)| squared+|q(x)| squared in
    Federer 3.3.5, p. 292. The actual independent orthogonal-chart
    laws identify the base projection and normal coordinates. *)
Lemma structure_projection_chart_squared_norm (R:realType) k m
    (p:{linear R_n R (k+m)->R_n R m})
    (F G:{linear R_n R (k+m)->R_n R (k+m)}):
  is_orthogonal_projection_chart p F G ->forall x,
    (inner_norm (@euclidean_inner_productP R (k+m)) x)^+2=
      (inner_norm (@euclidean_inner_productP R k) (@euclidean_first_block R k m (F x)))^+2+
      (inner_norm (@euclidean_inner_productP R m) (p x))^+2.
Proof.
move=>hChart x.
have hEnergy:=@structure_block_squared_norm R k m (F x).
have hP:@euclidean_last_block R k m (F x)=p x.
  exact:projection_chart_coordinate_law hChart x.
have hTail:(\sum_i ((@euclidean_last_block R k m (F x)) i)^+2)=
    (inner_norm (@euclidean_inner_productP R m) (p x))^+2.
  rewrite -hP inner_norm_sqr /euclidean_inner_product.
  apply:eq_bigr=>i _; exact:expr2.
by rewrite (orthogonal_map_norm (@euclidean_inner_productP R (k+m))
  (@euclidean_inner_productP R (k+m)) (projection_chart_orthogonal_law hChart)) hTail in hEnergy.
Qed.

(** Source for [structure_transverse_inverse_distance]: the bound
    Lip(q composed with (p restricted to S) inverse)<=sqrt(s inverse
    squared minus one), Federer 3.3.5, p. 292. It follows from the
    proved original inverse-distance inequality and the actual norm
    decomposition, with no supplied transverse bound. *)
Theorem structure_transverse_inverse_distance (R:realType) k m (hmn:(m<=k+m)%N)
    (E S:set (inner_metric_space (@euclidean_inner_productP R (k+m))))
    (p:euclidean_projection_space R (k+m) m)
    (F G:{linear R_n R (k+m)->R_n R (k+m)}) (r: \bar R) (s C:R):
  is_orthogonal_projection_chart (euclidean_projection_linear p) F G ->
  0<s<1 ->0<=C ->C^+2=s^-1^+2-1 ->
  is_structure_cone_avoiding hmn E p r s ->S `<=` E ->
  (extended_metric_diameter S<r)%E ->
  forall x y,S x ->S y ->
    mdist (@euclidean_first_block R k m (F x):inner_metric_space (@euclidean_inner_productP R k))
      (@euclidean_first_block R k m (F y))<=
    C*mdist (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p y).
Proof.
move=>hChart /andP [hs hs1] hC hSquare hAvoid hSE hDiameter x y hx hy.
have hOriginal:=@structure_cone_avoidance_inverse_distance R (k+m) m hmn E S p r s
  hs hAvoid hSE hDiameter x y hx hy.
rewrite !inner_metric_distanceE -linearB in hOriginal.
have hEnergy:=structure_projection_chart_squared_norm hChart (x-y).
have hNX:0<=inner_norm (@euclidean_inner_productP R (k+m)) (x-y):=inner_norm_nonnegative _ _.
have hNP:0<=inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear p (x-y)):=inner_norm_nonnegative _ _.
have hNQ:0<=inner_norm (@euclidean_inner_productP R k) (@euclidean_first_block R k m (F (x-y))):=inner_norm_nonnegative _ _.
have hInv:0<=s^-1 by rewrite invr_ge0 ltW.
have hBoundSquare:(inner_norm (@euclidean_inner_productP R (k+m)) (x-y))^+2<=
    (s^-1)^+2*(inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear p (x-y)))^+2 by nra.
pose Q:=hom_comp (@euclidean_first_block_map R k m) (hom_of_linear F).
rewrite !inner_metric_distanceE.
change (is_true (inner_norm (@euclidean_inner_productP R k) (Q x-Q y)<=
  C*inner_norm (@euclidean_inner_productP R m)
    (euclidean_projection_linear p x-euclidean_projection_linear p y))).
have hQD:Q (x-y)=Q x-Q y:=linearB (hom_as_linear Q) x y.
rewrite -hQD -linearB.
change (is_true (inner_norm (@euclidean_inner_productP R k)
  (@euclidean_first_block R k m (F (x-y)))<=
  C*inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear p (x-y)))).
rewrite -(ler_sqr hNQ (mulr_ge0 hC hNP)) exprMn.
nra.
Qed.
