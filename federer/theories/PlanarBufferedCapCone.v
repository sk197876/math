(** Federer (1969), 3.3.19, p. 305: preserve
    both strict original cone inequalities by using a
    smaller local cap aperture. No original vertex is excluded. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP Bilinear
  InnerNorm InnerNormInequalities InnerMetric MetricClosedBalls InnerCapRadiusBound
  PlanarCircleCapCoordinates PlanarCapConeCoordinates PlanarProjectionUnitNormal
  EuclideanProjectionSpace StructureProjectionKernel StructureCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Buffer.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation N:=(inner_norm hE).

(** Source for [planar_buffered_cap_cone_inclusion]: corrected
    auxiliary cap-difference inclusion behind 3.3.19, p. 305.
    A smaller auxiliary sigma<s and sufficiently small original
    radial deficit put every closed cap-difference point in the
    ORIGINAL strict cone X(a,2rs,ker p,s), also when a
    is on the parent boundary. A nearby unit normal is
    allowed, as needed for the common angular-tail argument. *)
Theorem planar_buffered_cap_cone_inclusion
    (p:euclidean_projection_space R 2 1) (u eta e z x:E) (r d c sigma s:R) n:
  is_planar_projection_unit_normal p u ->is_planar_circle_frame eta e ->
  0<r ->0<=d ->d<=r ->r-2* r/n%:R<=d ->
  0<c ->0<sigma ->c^+2+sigma^+2= 1 ->sigma<s ->
  2/n%:R<2*(s-sigma) ->N (u-eta)<s-sigma ->
  metric_closed_ball z r x ->r* c<=B (x-z) (planar_rotated_frame_direction eta e c sigma) ->
  B (x-z) eta<r-2* r/n%:R ->
  structure_cone (structure_projection_kernel (leqnSn 1) p)
    (z+d*:eta) (2* r* s)%:E s x.
Proof.
move=>hNormal hFrame hr hd hdr hDeficit hc hSigma hUnit hAperture hSmall hNear hx hCap hBelow.
have hs:0<s by lra.
have hBelowVertex:B (x-z) eta<d by lra.
have [hPositive hCoordinate]:= @planar_cap_difference_normal_bound R eta e z x d r c sigma
  hFrame hc hSigma hUnit hdr hBelowVertex hCap.
have [hCapUnit hCapPair]:= @planar_rotated_frame_direction_laws R eta e c sigma hFrame hUnit.
have hCapRadius:= @inner_cap_boundary_radius_bound R (R_n R 2) B hE z eta
  (planar_rotated_frame_direction eta e c sigma) x r c sigma
  (ltW hr) (ltW hc) (ltW hSigma) hUnit hFrame.1 hCapUnit hCapPair hx hCap.
have hRadial:mdist (z+r*:eta) (z+d*:eta)= r-d.
  have hDifference:(z+r*:eta)-(z+d*:eta)=(r-d)*:eta.
    by rewrite opprD addrACA subrr add0r -scalerBl.
  have hNonnegative:0<=r-d by lra.
  by rewrite inner_metric_distanceE hDifference inner_normZ hFrame.1 mulr1 (ger0_norm hNonnegative).
have hTriangle:= metric_triangle x (z+r*:eta) (z+d*:eta).
rewrite hRadial in hTriangle.
have hScaled:r*(2/n%:R)<r*(2*(s-sigma)) by rewrite ltr_pM2l.
have hRadius:mdist x (z+d*:eta)<2* r* s by nra.
pose v:= x-(z+d*:eta).
have hCauchy:= inner_cauchy hE v (u-eta).
have hDot:B v u= B v eta+B v (u-eta).
  rewrite (bilBr (inner_bilinear hE));ring.
have hTriangleDot:`|B v u|<=`|B v eta|+`|B v (u-eta)|.
  rewrite hDot;exact:ler_normD.
have hNearScaled:N v* N (u-eta)<N v*(s-sigma) by rewrite ltr_pM2l.
have hSlope:`|B v u|<s* N v by nra.
apply:(@planar_projection_normal_coneE R p u (z+d*:eta) x (2* r* s)%:E s hNormal hs).2.
split;first exact:hSlope.
by rewrite -inner_metric_distanceE lte_fin.
Qed.
End Buffer.
