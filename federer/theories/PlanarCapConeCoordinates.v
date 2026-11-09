(** Federer (1969), 3.3.19, p. 305: actual cap
    differences control the normal coordinate relative to
    the original vertex; auxiliary apertures stay local. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP Bilinear
  InnerNorm InnerNormInequalities InnerMetric InnerCapRadiusBound PlanarCircleCapCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation N:=(inner_norm hE).

(** Source for [planar_rotated_frame_direction]: the actual
    direction eta exp(i alpha), with c= cos(alpha) and
    s= sin(alpha), in the cap of 3.3.19, p. 305.
    The independently specified local frame determines it. *)
Definition planar_rotated_frame_direction (eta e:E) (c s:R):E:= c*:eta+s*:e.

(** Source for [planar_rotated_frame_direction_laws]: the
    rotated cap normal has unit norm and dot product c
    with eta, by the actual orthonormal frame laws.
    These support 3.3.19, p. 305. *)
Lemma planar_rotated_frame_direction_laws (eta e:E) (c s:R):
  is_planar_circle_frame eta e ->c^+2+s^+2= 1 ->
  N (planar_rotated_frame_direction eta e c s)= 1 /\
  B eta (planar_rotated_frame_direction eta e c s)= c.
Proof.
move=>hFrame hUnit.
have hEta:B eta eta= 1 by rewrite -(inner_norm_sqr hE) hFrame.1 expr1n.
have he:B e e= 1 by rewrite -(inner_norm_sqr hE) hFrame.2.1 expr1n.
have hCross:B eta e= 0:= hFrame.2.2.1.
have hReverse:B e eta= 0 by rewrite (inner_symmetric hE) hCross.
split.
- apply:inner_norm_value;first exact:ler01.
  rewrite /planar_rotated_frame_direction expr1n
    (bilDl (inner_bilinear hE)) !(bilDr (inner_bilinear hE))
    !(bilZl (inner_bilinear hE)) !(bilZr (inner_bilinear hE)).
  change (1= c*(c* B eta eta)+c*(s* B eta e)+(s*(c* B e eta)+s*(s* B e e))).
  rewrite hEta he hCross hReverse;nra.
- rewrite /planar_rotated_frame_direction (bilDr (inner_bilinear hE))
    !(bilZr (inner_bilinear hE)) hEta hCross.
  change (c*1+s*0= c);ring.
Qed.

(** Source for [planar_cap_difference_normal_bound]: if the
    original vertex is z+d eta, d<=r, and an original
    cap point has eta-coordinate strictly below d, its
    normal coordinate relative to the vertex is at most
    s times its original distance. This is the closed
    geometric bound behind 3.3.19, p. 305; a smaller
    auxiliary s supplies the strict printed cone. *)
Theorem planar_cap_difference_normal_bound (eta e z x:E) (d r c s:R):
  is_planar_circle_frame eta e ->0<c ->0<s ->c^+2+s^+2= 1 ->d<=r ->
  B (x-z) eta<d ->r* c<=B (x-z) (planar_rotated_frame_direction eta e c s) ->
  0<N (x-(z+d*:eta)) /\
  `|B (x-(z+d*:eta)) eta|<=s* N (x-(z+d*:eta)).
Proof.
move=>hFrame hc hs hUnit hdr hBelow hCap.
pose X:= B (x-z) eta.
pose Y:= B (x-z) e.
pose q:= d-X.
have hq:0<q by rewrite /q /X;lra.
have hCapCoordinates:r* c<=c* X+s* Y.
  move:hCap;rewrite /planar_rotated_frame_direction (bilDr (inner_bilinear hE))
    !(bilZr (inner_bilinear hE)).
  change (r* c<=c* X+s* Y ->r* c<=c* X+s* Y);exact.
have hSlope:c* q<=s* Y by rewrite /q;nra.
have hY:0<Y by nra.
have hPairEta:B eta eta= 1 by rewrite -(inner_norm_sqr hE) hFrame.1 expr1n.
have hPairE:B eta e= 0:= hFrame.2.2.1.
have hVector:x-(z+d*:eta)=(x-z)-d*:eta by rewrite opprD addrA.
have hEta:B (x-(z+d*:eta)) eta= -q.
  rewrite hVector (bilBl (inner_bilinear hE)) (bilZl (inner_bilinear hE)) hPairEta.
  change (X-d*1= -q);rewrite /q;ring.
have he:B (x-(z+d*:eta)) e= Y.
  rewrite hVector (bilBl (inner_bilinear hE)) (bilZl (inner_bilinear hE)) hPairE.
  change (Y-d*0= Y);ring.
have hSquare:(N (x-(z+d*:eta)))^+2= q^+2+Y^+2.
  rewrite hFrame.2.2.2 (inner_symmetric hE eta (x-(z+d*:eta)))
    (inner_symmetric hE e (x-(z+d*:eta))) hEta he;ring.
have hNonnegative:= inner_norm_nonnegative hE (x-(z+d*:eta)).
have hPositive:0<N (x-(z+d*:eta)) by nra.
split=>//.
rewrite hEta normrN (ger0_norm (ltW hq)).
rewrite -(ler_sqr (ltW hq) (mulr_ge0 (ltW hs) hNonnegative)) exprMn hSquare.
have hLeft:0<=c* q by apply:mulr_ge0;exact:ltW.
have hRight:0<=s* Y by apply:mulr_ge0;exact:ltW.
have hSlopeSquare:(c* q)^+2<=(s* Y)^+2 by rewrite ler_sqr.
have hScaled:= congr1 (fun t:R=>q^+2* t) hUnit.
nra.
Qed.
End Coordinates.
