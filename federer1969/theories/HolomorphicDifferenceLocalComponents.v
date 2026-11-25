(** Federer (1969), 3.4.12, p. 339: use the real case
    to prove local component finiteness for holomorphic differences.
    The original squared-modulus equations and exact paired real
    coordinate isomorphism give the real analytic variety germs.
    Apply the already proved 3.4.9 component theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  StandardHermitianCoordinates HolomorphicCoordinateNorm ComplexEuclideanCoordinates
  ComplexEuclideanCoordinateTopology HolomorphicVarietyGermUP HolomorphicVarietyGermReal
  FiniteAnalyticVarietyLinearPreimage AnalyticDifferenceLocalComponents LocalComponentInverseTransport
  SetGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
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
(** Source for [holomorphic_difference_local_components]: the
    actual components of the difference of two original holomorphic
    varieties form a locally finite family. This supplies the
    component-finiteness argument explicitly permitted in 3.4.12,
    p. 339, through the proved real theorem 3.4.9, p. 337. *)
Theorem holomorphic_difference_local_components (S D:set X) a:
  @is_holomorphic_variety_germ R X NX hNX a (@set_germ TX a S) ->
  @is_holomorphic_variety_germ R X NX hNX a (@set_germ TX a D) ->
  exists O:set X,@open TX O /\O a /\
    finite_set (@connected_component TX (S `\` D) @` ((S `\` D) `&` O)).
Proof.
move=>hS hD.
pose u:=@complex_from_real_coordinate_hom R n.
pose v:=@complex_real_coordinate_hom R n.
have hU:continuous (fun y:TY=>(u y:TX)):=@complex_from_real_coordinate_hom_continuous R n.
have hV:continuous (fun x:TX=>(v x:TY)):=@complex_real_coordinate_hom_continuous R n.
have hUV:cancel v u:=@complex_real_coordinatesK R n.
have hVU:cancel u v:=@complex_from_real_coordinatesK R n.
have hSReal:=holomorphic_variety_germ_real hS.
have hDReal:=holomorphic_variety_germ_real hD.
have hSPre:=@analytic_variety_germ_linear_preimage R Y XR NY NX hNY hNX u (v a) a S
  (@complex_from_real_coordinate_hom_bounded R n) (hUV a) hSReal.
have hDPre:=@analytic_variety_germ_linear_preimage R Y XR NY NX hNY hNX u (v a) a D
  (@complex_from_real_coordinate_hom_bounded R n) (hUV a) hDReal.
have [O [hO [hOA hFinite]]]:=@analytic_difference_local_components R (n+n)
  (u @^-1` S) (u @^-1` D) (v a) hSPre hDPre.
have hSame:u @^-1` (S `\` D)=(u @^-1` S) `\` (u @^-1` D) by [].
rewrite -hSame in hFinite.
exists (v @^-1` O);split.
- exact:(@open_comp TX TY v O (fun x _=>hV x) hO).
split;first exact:hOA.
exact:(@local_component_inverse_transport TY TX u v (S `\` D) O hU hV hVU hUV hFinite).
Qed.
End Components.
