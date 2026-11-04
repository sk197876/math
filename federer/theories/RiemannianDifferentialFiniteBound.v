(** Federer (1969), 3.2.46, p. 282: an
    original Lipschitz map has uniformly bounded actual
    differentials in its two original metric forms.
    A finite auxiliary bound suffices for the signed
    3.2.12 reduction. No sharp Lipschitz constant
    formula or selected derivative field is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology ring.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness PositiveSymmetricNormFactor
  RiemannianTensorUP RiemannianMetricCarrier RiemannianMapDifferential
  RiemannianMapDifferentialUP RiemannianLocalMetricComparison RiemannianChartEllipsoid
  RiemannianChartOpenImages RiemannianPathLipschitz
  NormDifferentialUP NormDifferentialLocalIncrementBound FiniteNormDifferentialTransport
  NormFiniteLinearBound NormLinearDomainLaws EuclideanPartitionOverlapNeighborhood
  PartialFunctionUP LipschitzUP NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_differential_finite_bound]:
    the uniform derivative bound needed for the signed
    coarea extension of 3.2.46, p. 282, from
    3.1.1, p. 209. Two local metric comparisons
    at factor two give the finite bound 4K from
    a genuine finite-carrier Lipschitz bound K. Only
    existence of a uniform bound is used downstream;
    no sharp-constant identity is claimed. *)
Theorem riemannian_differential_finite_bound (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) (K : R) :
  0<K -> is_metric_lipschitz_bound setT f K ->
  forall a D, partial_function_graph (riemannian_map_differential f) a D -> forall v,
    inner_norm (riemannian_tensor_inner hh (set_valP (f a))) (D v)<=
      (4*K)*inner_norm (riemannian_tensor_inner hg (set_valP a)) v.
Proof.
move=> hK hBound a D hD.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose NE := inner_norm (@euclidean_inner_productP R m).
pose NF := inner_norm (@euclidean_inner_productP R n).
pose hNE := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNF := inner_norm_real_norm (@euclidean_inner_productP R n).
pose hB := riemannian_tensor_inner hg (set_valP a).
pose hC := riemannian_tensor_inner hh (set_valP (f a)).
pose NX := inner_norm hB.
pose NY := inner_norm hC.
pose hNX := inner_norm_real_norm hB.
pose hNY := inner_norm_real_norm hC.
have hCont : continuous f.
  apply:(@metric_fixed_lipschitz_continuous R X Y f K (ltW hK)).
  by move=> x y; exact:hBound.2 x y Logic.I Logic.I.
have [F [hF hDF]] := (riemannian_map_differential_graph f a D).1 hD.
have hFrozenD := @norm_differential_finite_norm_change R (R_n R m) (R_n R n)
  NE NX NF NY hNE hNX hNF hNY m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n) A F (val a) D hDF.
apply:(@norm_differential_local_increment_bound R (R_n R m) (R_n R n) NX NY hNX hNY
  A F (val a) D (4*K) hFrozenD).
have hTwo : (1<2 :> R) by rewrite ltr1n.
have [L [r [hr [hL [hPatchSource hSource]]]]] :=
  @riemannian_local_metric_comparison R m A g hg (val a) (set_valP a) 2 hTwo.
have [M [s [hs [hM [hPatchTarget hTarget]]]]] :=
  @riemannian_local_metric_comparison R n B h hh (val (f a)) (set_valP (f a)) 2 hTwo.
pose V1 := [set x : X | NE (L (val x-val a))<r].
pose V2 := [set y : Y | NF (M (val y-val (f a)))<s].
pose V := V1 `&` f @^-1` V2.
have hV : open V.
  apply:openI; first exact:riemannian_chart_ellipsoid_open.
  exact:(@open_comp X Y f V2 (fun x _=>hCont x)
    (@riemannian_chart_ellipsoid_open R n B h hh M (val (f a)) s)).
have hVa : V a.
  split.
  - change (is_true (NE (L (val a-val a))<r)); by rewrite subrr linear0 /NE inner_norm0.
  - change (is_true (NF (M (val (f a)-val (f a)))<s)); by rewrite subrr linear0 /NF inner_norm0.
pose W := (fun x : X=>(val x : E)) @` V.
have hW : @open E W := @riemannian_chart_open_coordinate_image R m A g hg V hV.
have hWa : W (val a) by exists a.
have hInterior := @inner_open_norm_domain R (R_n R m) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) W hW (val a) hWa.
have hIdentity := @norm_finite_linear_bounded R (R_n R m) (R_n R m) NX NE hNX hNE
  m (@coordinate_basis R m) (@coordinate_basisP R m) (hom_of_linear (linear_id (R_n R m))).
have [d [hd hNear]] := @norm_bounded_linear_preimage_interior R (R_n R m) (R_n R m)
  NX NE hNX (hom_of_linear (linear_id (R_n R m))) W (val a) hIdentity hInterior.
exists d; split; first exact hd.
move=> v hv.
have [x hx hValue] : W (val a+v) := hNear v hv.
have hDelta : val x-val a=v by rewrite hValue addrAC subrr add0r.
have hCoord : F (val a+v)-F (val a)=val (f x)-val (f a) by rewrite -hValue (hF x) (hF a).
have hSourceCentre : NE (L (val a-val a))<=r by rewrite subrr linear0 /NE inner_norm0; exact:ltW hr.
have hTargetCentre : NF (M (val (f a)-val (f a)))<=s by rewrite subrr linear0 /NF inner_norm0; exact:ltW hs.
have hSourceEstimate := (hSource a x hSourceCentre (ltW hx.1)).2.
have hTargetEstimate := (hTarget (f a) (f x) hTargetCentre (ltW hx.2)).1.
have hScaled := ler_wpM2l (@ler0n R 2) hTargetEstimate.
have hTwoNe : (2:R)!=0 by rewrite pnatr_eq0.
rewrite mulrA (mulfV hTwoNe) mul1r in hScaled.
have hMap := hBound.2 a x Logic.I Logic.I.
have hMiddle := ler_wpM2l (@ler0n R 2)
  (le_trans hMap (ler_wpM2l (ltW hK) hSourceEstimate)).
have hTotal := le_trans hScaled hMiddle.
rewrite hDelta (positive_norm_factor_norm hL) in hTotal.
have hCoeff : 2*(K*(2*NX v))=(4*K)*NX v by ring.
rewrite hCoeff in hTotal.
rewrite /NY hCoord -(positive_norm_factor_norm hM); exact hTotal.
Qed.
