(** Federer (1969), 3.4.12, p. 339: use the real case
    to prove local component finiteness for holomorphic differences.
    The original squared-modulus equations and exact paired real
    coordinate isomorphism give the real analytic variety germs.
    Apply the already proved 3.4.9 component theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FunctionalHolomorphicDifference FunctionalHolomorphicSubmanifoldUP FiniteAnalyticVarietyLinearPreimage HolomorphicVarietyReal Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  StandardHermitianCoordinates HolomorphicCoordinateNorm ComplexEuclideanCoordinates
  ComplexEuclideanCoordinateTopology HolomorphicVarietyGermUP HolomorphicVarietyGermReal
  FiniteAnalyticVarietyLinearPreimage AnalyticDifferenceBallComponents LocalComponentInverseTransport
  SetGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Components.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Y:=(R_n R (n+n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (n+n))).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
Local Notation TX:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
(** Source for [functional_holomorphic_ball_finite_components]: every
    sufficiently small ball retains finite original stratum components,
    3.4.9, p. 337, under 3.4.12, p. 339. The sphere
    cut is real analytic; no holomorphy is asserted for it. *)
Theorem functional_holomorphic_ball_finite_components m (U S:set X) r:
  @is_functional_holomorphic_submanifold R n m U S ->0<r ->
  [set x|NX x<=r] `<=` U ->
  finite_set (@connected_component TX (S `&` [set x|NX x<r]) @`
    (S `&` [set x|NX x<r])).
Proof.
move=>hS hR hKU.
pose u:=@complex_from_real_coordinate_hom R n.
pose v:=@complex_real_coordinate_hom R n.
have hU:continuous (fun y:TY=>(u y:TX)):=@complex_from_real_coordinate_hom_continuous R n.
have hV:continuous (fun x:TX=>(v x:TY)):=@complex_real_coordinate_hom_continuous R n.
have hUV:cancel v u:=@complex_real_coordinatesK R n.
have hVU:cancel u v:=@complex_from_real_coordinatesK R n.
have [H [N [hH [hN hDifference]]]]:=functional_holomorphic_difference hS.
have hHReal:=@finite_analytic_variety_linear_preimage R Y XR NY NX hNY hNX u U H
  (@complex_from_real_coordinate_hom_bounded R n) (holomorphic_variety_real_analytic hH).
have hNReal:=@finite_analytic_variety_linear_preimage R Y XR NY NX hNY hNX u U N
  (@complex_from_real_coordinate_hom_bounded R n) (holomorphic_variety_real_analytic hN).
have hNorm y:NX (u y)=NY y:=@complex_inverse_euclidean_coordinate_norm R n y.
have hInside:[set y|NY y<=r] `<=` (u @^-1` U).
  move=>y hy;apply:(hKU (u y));change (is_true (NX (u y)<=r));by rewrite hNorm.
have hFinite:=@analytic_difference_ball_finite_components R (n+n)
  (u @^-1` U) (u @^-1` H) (u @^-1` N) r hHReal hNReal hR hInside.
pose A:set X:=S `&` [set x|NX x<r].
have hSame:u @^-1` A=((u @^-1` H) `\` (u @^-1` N)) `&` [set y|NY y<r].
  apply:funext=>y;rewrite /A /= hNorm;by rewrite hDifference.
have hAll:finite_set (@connected_component TY (u @^-1` A) @` ((u @^-1` A) `&` setT)).
  by rewrite setIT hSame.
have hTransport:=@local_component_inverse_transport TY TX u v A setT hU hV hVU hUV hAll.
have hFull:v @^-1` setT=setT by [].
by rewrite hFull setIT in hTransport.
Qed.
End Components.
