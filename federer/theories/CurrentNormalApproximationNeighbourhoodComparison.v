(** Federer (1969), 4.1.14, p. 370: normal smooth
    image limits do not depend on the source neighbourhood.
    Compare two original families on the intersection of
    their source neighbourhoods, identify the same restricted
    current by transitivity, and apply the preceding normal
    comparison there. All derivative caps stay on K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormLinearDomainLaws NormRegularity NormClassOneUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP OpenLocalLipschitzCompact
  SmoothCompactSet SmoothCompactSetExtensionality CurrentSpaces NormalCurrentsUP
  CurrentSupportGeometry CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentOpenRestrictionNormal CurrentOpenRestrictionTransitive
  CurrentNormalNeighbourhoodPushforward CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentLipschitzCompactImage
  CurrentSmoothApproximationUP CurrentApproximationOpenRestriction
  CurrentNormalSmoothApproximationCauchy CurrentFlatNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_normal_neighbourhood_compact_image]:
    use the original compact-map interface on both sides
    of the neighbourhood identity in 4.1.13, pp. 369–370,
    supporting Federer 4.1.14, p. 370. Every compactness
    witness for the smaller actual current is allowed. *)
Lemma current_normal_neighbourhood_compact_image (R:realType) (h2:(1+1:R)!=0)
    n nu m (W Z:set (R_n R n)) (V:set (R_n R nu))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) Z x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (hWZ:forall x,W x->Z x) (f:R_n R n->R_n R nu)
    (hImage:forall x,Z x->V (f x))
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) Z f)
    (hImageSmall:forall x,W x->V (f x))
    (hfSmall:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) W f)
    (T:@current_space R h2 n Z hZ m)
    (hNormal:@is_normal_current R h2 n Z hZ m T)
    (hSupport:@current_support R h2 n Z hZ m T `<=` W)
    (hCompactSmall:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n W hW m
        (@current_open_restriction R h2 n m W Z hW hZ hWZ T))):
  @current_compact_map_pushforward R h2 n nu Z V hZ hV f hImage hf m T hNormal.2=
  @current_compact_map_pushforward R h2 n nu W V hW hV f hImageSmall hfSmall m
    (@current_open_restriction R h2 n m W Z hW hZ hWZ T) hCompactSmall.
Proof.
pose hpSmall:=@current_compact_map_proper R h2 n nu m W V hW
  (@current_open_restriction R h2 n m W Z hW hZ hWZ T)
  f hImageSmall (norm_class_continuous (hfSmall 0%N)) hCompactSmall.
exact:(@current_normal_neighbourhood_pushforward R h2 n nu m W Z V
  hW hZ hV hWZ f hImage hf hImageSmall hfSmall T hNormal hSupport hpSmall).
Qed.

Section CurrentNormalApproximationNeighbourhoodComparison.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Variable T:@current_space R h2 n U hU m.
Hypothesis hNormal:@is_normal_current R h2 n U hU m T.
Hypothesis hSupport:@current_support R h2 n U hU m T `<=` smooth_compact_carrier K.
Arguments hSupport : clear implicits.
Variables Z0 Z1:set X.
Hypothesis hZ0:forall x,Z0 x->norm_domain_interior NX Z0 x.
Hypothesis hZ1:forall x,Z1 x->norm_domain_interior NX Z1 x.
Hypothesis hZ0U:forall x,Z0 x->U x.
Arguments hZ0U : clear implicits.
Hypothesis hZ1U:forall x,Z1 x->U x.
Arguments hZ1U : clear implicits.
Hypothesis hKZ0:smooth_compact_carrier K `<=` Z0.
Arguments hKZ0 : clear implicits.
Hypothesis hKZ1:smooth_compact_carrier K `<=` Z1.
Arguments hKZ1 : clear implicits.
Local Notation K0 := (@current_compact_index_in_open R n U Z0 K hKZ0).
Local Notation K1 := (@current_compact_index_in_open R n U Z1 K hKZ1).
Local Notation T0 := (@current_open_restriction R h2 n m Z0 U hZ0 hU hZ0U T).
Local Notation T1 := (@current_open_restriction R h2 n m Z1 U hZ1 hU hZ1U T).
Local Notation hNormal0 := (@current_normal_neighbourhood_restriction R h2 n
  Z0 U hZ0 hU hZ0U m T hNormal (fun x hx=>hKZ0 x (hSupport x hx))).
Local Notation hNormal1 := (@current_normal_neighbourhood_restriction R h2 n
  Z1 U hZ1 hU hZ1U m T hNormal (fun x hx=>hKZ1 x (hSupport x hx))).
Variables g q:nat->X->Y.
Hypothesis hG:@is_current_smooth_approximation R n nu Z0 V K0 f g.
Hypothesis hQ:@is_current_smooth_approximation R n nu Z1 V K1 f q.
Local Notation u0 := (fun i=>@current_compact_map_pushforward R h2 n nu Z0 V hZ0 hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m T0 hNormal0.2).
Local Notation u1 := (fun i=>@current_compact_map_pushforward R h2 n nu Z1 V hZ1 hV
  (q i) (current_smooth_approximation_image hQ i)
  (current_smooth_approximation_class hQ i) m T1 hNormal1.2).

(** Source for [current_normal_approximation_neighbourhoods_compare]:
    two original smooth families on arbitrary neighbourhoods
    of K have images arbitrarily close in every prescribed
    F_E, independently in their eventual indices, supporting
    the first independence paragraph of Federer 4.1.14,
    p. 370. Normality and both restricted currents are
    derived from the original T. No global derivative
    cap, convexity or strengthened image premise is added. *)
Theorem current_normal_approximation_neighbourhoods_compare
    (E:smooth_compact_set hNY V)
    (hInterior:forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)):
  forall epsilon:R,0<epsilon->exists N:nat,forall i j:nat,
    (N<=i)%N->(N<=j)%N->
    (@current_flat_norm R h2 nu m V hV E (u1 j-u0 i)<epsilon%:E)%E.
Proof.
pose W:=Z0 `&` Z1.
pose hW:=fun x (hx:W x)=>@norm_domain_intersection_interior R X NX Z0 Z1 x
  (@hZ0 x hx.1) (@hZ1 x hx.2).
pose hWZ0:=fun x (hx:W x)=>hx.1.
pose hWZ1:=fun x (hx:W x)=>hx.2.
pose hWU:=fun x (hx:W x)=>hZ0U x hx.1.
pose hKW:=fun x (hx:smooth_compact_carrier K x)=>conj (hKZ0 x hx) (hKZ1 x hx).
pose KW:=@current_compact_index_in_open R n U W K hKW.
pose S:=@current_open_restriction R h2 n m W U hW hU hWU T.
pose hTSW:=fun x (hx:@current_support R h2 n U hU m T x)=>hKW x (hSupport x hx).
pose hNS:=@current_normal_neighbourhood_restriction R h2 n W U hW hU hWU
  m T hNormal hTSW.
have hSSupport:@current_support R h2 n W hW m S `<=` smooth_compact_carrier KW.
  move=>x hx;apply:hSupport.
  exact:(@current_open_restriction_support_subset R h2 n m W U hW hU hWU T x hx).
pose hK0W:=fun x (hx:smooth_compact_carrier K0 x)=>hKW x hx.
pose hK1W:=fun x (hx:smooth_compact_carrier K1 x)=>hKW x hx.
have hIndex0:@current_compact_index_in_open R n Z0 W K0 hK0W=KW.
  apply:smooth_compact_set_extensionality;by [].
have hIndex1:@current_compact_index_in_open R n Z1 W K1 hK1W=KW.
  apply:smooth_compact_set_extensionality;by [].
have hGW:=@current_smooth_approximation_open_restriction R n nu
  Z0 W V hW hWZ0 K0 hK0W f g hG.
have hQW:=@current_smooth_approximation_open_restriction R n nu
  Z1 W V hW hWZ1 K1 hK1W f q hQ.
rewrite hIndex0 in hGW;rewrite hIndex1 in hQW.
pose hFImage:=fun x (hx:W x)=>hImage x (hWU x hx).
pose hFLocal:=@metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U W f hWU hLocal.
pose hFContinuous:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY
  W f hW hFLocal.
have hR0:@current_open_restriction R h2 n m W Z0 hW hZ0 hWZ0 T0=S.
  exact:(@current_open_restriction_transitive R h2 n m W Z0 U
    hW hZ0 hU hWZ0 hZ0U hWU T).
have hR1:@current_open_restriction R h2 n m W Z1 hW hZ1 hWZ1 T1=S.
  exact:(@current_open_restriction_transitive R h2 n m W Z1 U
    hW hZ1 hU hWZ1 hZ1U hWU T).
have hT0W:@current_support R h2 n Z0 hZ0 m T0 `<=` W.
  move=>x hx.
  have hxT:=@current_open_restriction_support_subset R h2 n m Z0 U hZ0 hU hZ0U T x hx.
  exact:(@hTSW x hxT).
have hT1W:@current_support R h2 n Z1 hZ1 m T1 `<=` W.
  move=>x hx.
  have hxT:=@current_open_restriction_support_subset R h2 n m Z1 U hZ1 hU hZ1U T x hx.
  exact:(@hTSW x hxT).
pose hN00:=@current_normal_neighbourhood_restriction R h2 n W Z0 hW hZ0 hWZ0
  m T0 hNormal0 hT0W.
pose hN11:=@current_normal_neighbourhood_restriction R h2 n W Z1 hW hZ1 hWZ1
  m T1 hNormal1 hT1W.
pose v0:=fun i=>@current_compact_map_pushforward R h2 n nu W V hW hV
  (g i) (current_smooth_approximation_image hGW i)
  (current_smooth_approximation_class hGW i) m S hNS.2.
pose v1:=fun i=>@current_compact_map_pushforward R h2 n nu W V hW hV
  (q i) (current_smooth_approximation_image hQW i)
  (current_smooth_approximation_class hQW i) m S hNS.2.
have hImage0 i:u0 i=v0 i.
  have hFirst:=@current_normal_neighbourhood_compact_image R h2 n nu m
    W Z0 V hW hZ0 hV hWZ0 (g i)
    (current_smooth_approximation_image hG i) (current_smooth_approximation_class hG i)
    (current_smooth_approximation_image hGW i) (current_smooth_approximation_class hGW i)
    T0 hNormal0 hT0W hN00.2.
  apply:eq_trans hFirst _.
  exact:(@current_compact_map_pushforward_congruence R h2 n nu W V hW hV
    (g i) (current_smooth_approximation_image hGW i)
    (current_smooth_approximation_class hGW i) m _ S hN00.2 hNS.2 hR0).
have hImage1 i:u1 i=v1 i.
  have hFirst:=@current_normal_neighbourhood_compact_image R h2 n nu m
    W Z1 V hW hZ1 hV hWZ1 (q i)
    (current_smooth_approximation_image hQ i) (current_smooth_approximation_class hQ i)
    (current_smooth_approximation_image hQW i) (current_smooth_approximation_class hQW i)
    T1 hNormal1 hT1W hN11.2.
  apply:eq_trans hFirst _.
  exact:(@current_compact_map_pushforward_congruence R h2 n nu W V hW hV
    (q i) (current_smooth_approximation_image hQW i)
    (current_smooth_approximation_class hQW i) m _ S hN11.2 hNS.2 hR1).
move=>epsilon hEpsilon.
have[N hN]:=@current_normal_smooth_approximations_compare R h2 n nu W V hW hV
  KW f hFImage hFContinuous g q hGW hQW m S hNS hSSupport E hInterior epsilon hEpsilon.
exists N=>i j hi hj.
have hDifference:=hN i j hi hj.
change (is_true (@current_flat_norm R h2 nu m V hV E (v1 j-v0 i)<epsilon%:E)%E)
  in hDifference.
by rewrite -(hImage1 j) -(hImage0 i) in hDifference.
Qed.
End CurrentNormalApproximationNeighbourhoodComparison.
