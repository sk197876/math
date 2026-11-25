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
  FiniteAnalyticVarietyLinearPreimage AnalyticDifferenceFiniteNeighbourhood LocalComponentInverseTransport
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
(** Source for [holomorphic_difference_finite_neighbourhood]:
    the real-case component argument allowed by 3.4.12, p. 339,
    applied to the original holomorphic difference inside any
    prescribed open neighbourhood. Count components of the restricted
    set itself; arbitrary restriction of a finite component family
    would not prove this assertion. *)
Theorem holomorphic_difference_finite_neighbourhood (S D:set X):
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ TX 0 S) ->
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ TX 0 D) ->
  forall N:set X,@open TX N ->N 0 ->
    exists O:set X,@open TX O /\O 0 /\O `<=` N /\
      finite_set (@connected_component TX (O `&` (S `\` D)) @` (O `&` (S `\` D))).
Proof.
move=>hS hD N hN hN0.
pose u:=@complex_from_real_coordinate_hom R n.
pose v:=@complex_real_coordinate_hom R n.
have hU:continuous (fun y:TY=>(u y:TX)):=@complex_from_real_coordinate_hom_continuous R n.
have hV:continuous (fun x:TX=>(v x:TY)):=@complex_real_coordinate_hom_continuous R n.
have hUV:cancel v u:=@complex_real_coordinatesK R n.
have hVU:cancel u v:=@complex_from_real_coordinatesK R n.
have hSReal:=holomorphic_variety_germ_real hS.
have hDReal:=holomorphic_variety_germ_real hD.
have hU0:u 0 = 0 by rewrite /u linear0.
have hV0:v 0 = 0 by rewrite /v linear0.
have hSPre:=@analytic_variety_germ_linear_preimage R Y XR NY NX hNY hNX u 0 0 S
  (@complex_from_real_coordinate_hom_bounded R n) hU0 hSReal.
have hDPre:=@analytic_variety_germ_linear_preimage R Y XR NY NX hNY hNX u 0 0 D
  (@complex_from_real_coordinate_hom_bounded R n) hU0 hDReal.
have hNPre:@open TY (u @^-1` N):=@open_comp TY TX u N (fun x _=>hU x) hN.
have hNPre0:(u @^-1` N) 0 by change (N (u 0));rewrite hU0.
have [W [hW [hW0 [hWN hFinite]]]]:=@analytic_difference_finite_neighbourhood R (n+n)
  (u @^-1` S) (u @^-1` D) hSPre hDPre (u @^-1` N) hNPre hNPre0.
pose O:set X:=v @^-1` W.
pose H:set X:=O `&` (S `\` D).
have hSame:u @^-1` H = W `&` ((u @^-1` S) `\` (u @^-1` D)).
  apply/seteqP;split=>y [hy hd];split;try exact:hd.
  - by change (W (v (u y))) in hy;rewrite hVU in hy.
  - change (W (v (u y)));by rewrite hVU.
have hFinitePre:finite_set (@connected_component TY (u @^-1` H) @` ((u @^-1` H) `&` setT)).
  by rewrite setIT hSame.
have hTransport:=@local_component_inverse_transport TY TX u v H setT hU hV hVU hUV hFinitePre.
have hAll:v @^-1` setT = setT by [].
rewrite hAll setIT in hTransport.
exists O;split.
- exact:(@open_comp TX TY v W (fun x _=>hV x) hW).
split;first by change (W (v 0));rewrite hV0.
split;last exact:hTransport.
move=>x hx;have h:=hWN (v x) hx;change (N (u (v x))) in h;by rewrite hUV in h.
Qed.
End Components.
