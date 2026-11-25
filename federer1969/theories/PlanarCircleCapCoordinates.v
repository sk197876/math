(** Federer 2.10.2(1), p. 171, supporting the actual circle example.
    Independent orthonormal-frame laws precede local existence. A unit
    cap has an inverse-Lipschitz transverse coordinate. No frame is
    globally selected and no arc-length formula is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra ring.
From Federer Require Import GrassmannAbbreviations InnerProductUP Bilinear
  EuclideanInnerProduct InnerNorm InnerNormInequalities InnerMetric
  RealMetricBackground MetricBiLipschitzUP LipschitzUP PlanarCircleCapScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_euclidean_inner_coordinates]: Federer 2.10.2(1),
    p. 171; supporting two-coordinate instance of the usual dot product
    from 1.7.1, p. 28. *)
Lemma planar_euclidean_inner_coordinates (R:realType) (x y:R_n R 2):
  euclidean_inner_product x y=
    x ord0*y ord0+x (@Ordinal 2 1 (erefl true))*y (@Ordinal 2 1 (erefl true)).
Proof.
rewrite /euclidean_inner_product !big_ord_recl big_ord0 !addr0.
have hi:(lift (ord0:'I_2) (ord0:'I_1))=(@Ordinal 2 1 (erefl true)) by apply:val_inj.
by rewrite hi.
Qed.

(** Source for [is_planar_circle_frame]: Federer 2.10.2(1), p. 171;
    supporting abstract orthonormal coordinates. Unit lengths,
    perpendicularity and exact Parseval are independent of any cap
    projection estimate or frame construction. *)
Definition is_planar_circle_frame (R:realType)
    (a e:inner_metric_space (@euclidean_inner_productP R 2)):Prop:=
  inner_norm (@euclidean_inner_productP R 2) a = 1 /\
  inner_norm (@euclidean_inner_productP R 2) e = 1 /\
  euclidean_inner_product a e = 0 /\
  forall x:R_n R 2, (inner_norm (@euclidean_inner_productP R 2) x)^+2=
    (euclidean_inner_product a x)^+2+(euclidean_inner_product e x)^+2.

(** Source for [planar_circle_frame_exists]: Federer 2.10.2(1),
    p. 171; supporting existence of local orthonormal coordinates for
    any original unit a. The perpendicular coordinate vector is used
    only as an existence witness, never as a chosen global frame. *)
Theorem planar_circle_frame_exists (R:realType)
    (a:inner_metric_space (@euclidean_inner_productP R 2)):
  inner_norm (@euclidean_inner_productP R 2) a = 1 ->
  exists e,is_planar_circle_frame a e.
Proof.
move=>ha.
pose i1:'I_2:=@Ordinal 2 1 (erefl true).
pose e:R_n R 2:=[ffun i=>if i==ord0 then -a i1 else a ord0].
have he0:e ord0= -a i1 by rewrite /e ffunE eqxx.
have he1:e i1=a ord0 by rewrite /e ffunE; by [].
have haSq:(a ord0)^+2+(a i1)^+2 = 1.
  have hh:=inner_norm_sqr (@euclidean_inner_productP R 2) a.
  rewrite ha expr1n planar_euclidean_inner_coordinates -!expr2 in hh.
  exact:esym hh.
exists e; split=>//; split.
- apply:inner_norm_value; first exact:ler01.
  rewrite expr1n planar_euclidean_inner_coordinates he0 he1; nra.
- split.
  + rewrite planar_euclidean_inner_coordinates he0 he1; ring.
  + move=>x; rewrite inner_norm_sqr !planar_euclidean_inner_coordinates he0 he1.
    have hPoly:(a ord0*x ord0+a i1*x i1)^+2+
        (-a i1*x ord0+a ord0*x i1)^+2=
        ((a ord0)^+2+(a i1)^+2)*(x ord0*x ord0+x i1*x i1) by ring.
    by rewrite hPoly haSq mul1r.
Qed.

(** Source for [planar_frame_projection_nonexpanding]: Federer
    2.10.2(1), p. 171; Cauchy's inequality for the actual transverse
    coordinate, used to compare its image diameter. *)
Lemma planar_frame_projection_nonexpanding (R:realType)
    (a e:inner_metric_space (@euclidean_inner_productP R 2))
    (hf:is_planar_circle_frame a e)
    (x y:inner_metric_space (@euclidean_inner_productP R 2)):
  mdist (euclidean_inner_product e x:real_line_metric R)
    (euclidean_inner_product e y:real_line_metric R)<=mdist x y.
Proof.
rewrite real_line_metric_distanceE inner_metric_distanceE.
have hh:=inner_cauchy (@euclidean_inner_productP R 2) e (x-y).
by rewrite (bilBr (inner_bilinear (@euclidean_inner_productP R 2))) hf.2.1 mul1r in hh.
Qed.

(** Source for [planar_frame_squared_distance]: Federer 2.10.2(1),
    p. 171; supporting exact squared chord in the independently specified
    frame, using only Parseval and bilinearity. *)
Lemma planar_frame_squared_distance (R:realType)
    (a e:inner_metric_space (@euclidean_inner_productP R 2))
    (hf:is_planar_circle_frame a e)
    (x y:inner_metric_space (@euclidean_inner_productP R 2)):
  (mdist x y)^+2=(euclidean_inner_product a x-euclidean_inner_product a y)^+2+
    (euclidean_inner_product e x-euclidean_inner_product e y)^+2.
Proof.
by rewrite inner_metric_distanceE hf.2.2.2
  !(bilBr (inner_bilinear (@euclidean_inner_productP R 2))).
Qed.

(** Source for [planar_unit_cap_projection_bilipschitz]: Federer
    2.10.2(1), p. 171; supporting uniform chord bound for a unit-circle
    cap. Projection is nonexpanding and its inverse has bound 1/delta.
    The cap and metric are the actual original ones. *)
Theorem planar_unit_cap_projection_bilipschitz (R:realType)
    (a e:inner_metric_space (@euclidean_inner_productP R 2))
    (hf:is_planar_circle_frame a e) (delta:R):
  0<delta -> delta<=1 ->
  is_metric_bilipschitz_bound
    [set x:inner_metric_space (@euclidean_inner_productP R 2)|
      inner_norm (@euclidean_inner_productP R 2) x = 1 /\delta<=euclidean_inner_product a x]
    (fun x=>(euclidean_inner_product e x:real_line_metric R)) delta^-1.
Proof.
move=>hd hd1.
have hInv:0<delta^-1 by rewrite invr_gt0.
have hOne:1<=delta^-1.
  have hh:=ler_wpM2r (ltW hInv) hd1.
  by rewrite mulfV ?gt_eqF // mul1r in hh.
split.
- split; first exact:ltW hInv.
  move=>x y _ _; apply:le_trans (planar_frame_projection_nonexpanding hf x y) _.
  have hh:=ler_wpM2r (mdist_ge0 x y) hOne.
  by rewrite mul1r in hh.
- move=>x y [hx hdx] [hy hdy].
  have hX:(euclidean_inner_product a x)^+2+(euclidean_inner_product e x)^+2 = 1.
    by rewrite -hf.2.2.2 hx expr1n.
  have hY:(euclidean_inner_product a y)^+2+(euclidean_inner_product e y)^+2 = 1.
    by rewrite -hf.2.2.2 hy expr1n.
  have hBound:=circle_cap_transverse_square_bound hd hdx hdy hX hY.
  have hDistance:=planar_frame_squared_distance hf x y.
  have hScaled:delta*mdist x y<=`|euclidean_inner_product e x-euclidean_inner_product e y|.
    rewrite -(ler_sqr (mulr_ge0 (ltW hd) (mdist_ge0 x y)) (normr_ge0 _)).
    rewrite exprMn -normrX ger0_norm ?sqr_ge0 // hDistance.
    exact:hBound.
  have hh:=ler_wpM2l (ltW hInv) hScaled.
  rewrite mulrA mulVf ?gt_eqF // mul1r in hh.
  by rewrite real_line_metric_distanceE.
Qed.
