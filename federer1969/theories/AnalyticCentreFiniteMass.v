(** Federer (1969), 3.4.10, p. 337:
    local finite mass at every actual centre.
    Reuse source translation and the proved invariance
    of Hausdorff measure under an isometric bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness SetGermUP
  AnalyticVarietyGermUP AnalyticSetLocalDepth AnalyticLocalFiniteMass
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_centre_local_finite_mass]: the
    local bound at each point used for
    the compact assertion of 3.4.10, p. 337.
    The actual original set and its original
    centre are retained after the isometric transport. *)
Theorem analytic_centre_local_finite_mass (R:realType) n (S:set (R_n R n)) a k:
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_analytic_variety_germ R (R_n R n) (inner_norm hB) hNX a (@set_germ T a S) ->
  (@analytic_set_local_depth R n S a<=k)%N ->
  exists W:set (R_n R n),@open T W /\W a /\
    (@hausdorff_measure R (inner_metric_space hB) k (S `&` W)< +oo)%E.
Proof.
move=>hB hNX T hAnalytic hBound.
pose X:=R_n R n;pose E:=inner_metric_space hB.
pose u:=fun x:T=>(a+x:T).
pose v:=fun x:T=>(x-a:T).
have hU:continuous u:=@real_norm_metric_translate_continuous R X (inner_norm hB) hNX a.
have hV:continuous v.
  have hSame:v=(fun x:T=>(-a+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hVU:cancel u v by move=>x;rewrite /u /v addrAC subrr add0r.
have hUV:cancel v u by move=>x;rewrite /u /v addrC subrK.
have hTranslated:=@analytic_set_translated_germ R n S a hAnalytic.
have [O [hO [hO0 hFinite]]]:=@analytic_origin_local_finite_mass R n (u @^-1` S) k
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
