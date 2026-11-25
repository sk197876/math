(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.10, p. 337:
    local finite mass at every actual centre.
    Reuse source translation and the proved invariance
    of Hausdorff measure under an isometric bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness SetGermUP
  HolomorphicVarietyGermUP HolomorphicSetLocalDepth HolomorphicLocalFiniteMass
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_centre_local_finite_mass]: the
    local bound at each point used for
    the compact assertion of 3.4.10, p. 337.
    The actual original set and its original
    centre are retained after the isometric transport. *)
Theorem holomorphic_centre_local_finite_mass (R:realType) n (S:set (coordinate_space (ComplexScalars.C R) n)) a k:
  let hB:=hermitian_real_inner_product (@standard_hermitian_productP R n) in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_holomorphic_variety_germ R (coordinate_space (ComplexScalars.C R) n) (inner_norm hB) hNX a (@set_germ T a S) ->
  (@holomorphic_set_local_depth R n S a<=k)%N ->
  exists W:set (coordinate_space (ComplexScalars.C R) n),@open T W /\W a /\
    (@hausdorff_measure R (inner_metric_space hB) (k+k) (S `&` W)< +oo)%E.
Proof.
move=>hB hNX T hHolomorphic hBound.
pose X:=coordinate_space (ComplexScalars.C R) n;pose E:=inner_metric_space hB.
pose u:=fun x:T=>(a+x:T).
pose v:=fun x:T=>(x-a:T).
have hU:continuous u:=@real_norm_metric_translate_continuous R (restricted_space (ComplexScalars.embed R) X) (inner_norm hB) hNX a.
have hV:continuous v.
  have hSame:v=(fun x:T=>(-a+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hVU:cancel u v by move=>x;rewrite /u /v addrAC subrr add0r.
have hUV:cancel v u by move=>x;rewrite /u /v addrC subrK.
have hTranslated:=@holomorphic_set_translated_germ R n S a hHolomorphic.
have [O [hO [hO0 hFinite]]]:=@holomorphic_origin_local_finite_mass R n (u @^-1` S) k
  hTranslated hBound.
exists (v @^-1` O);split.
- exact:(@open_comp T T v O (fun x _=>hV x) hO).
split;first by change (O (a-a));rewrite subrr.
have hDistance (x y:E):@mdist R E (u x) (u y)=@mdist R E x y.
  rewrite !inner_metric_distanceE.
  by rewrite /u opprD addrACA subrr add0r.
have hImage:u @` ((u @^-1` S) `&` O)=S `&` (v @^-1` O).
  apply/seteqP;split.
  + move=>x [y [hyS hyO] <-];split;first exact:hyS.
    by change (O (v (u y)));rewrite hVU.
  + move=>x [hxS hxO];exists (v x);last exact:hUV x.
    split;last exact:hxO;by change (S (u (v x)));rewrite hUV.
rewrite -hImage (@hausdorff_bijective_isometry_invariance R E E u v hVU hUV hDistance).
exact:hFinite.
Qed.
