(** Federer (1969), 3.4.5, p. 321,
    proved through 3.4.8(11), pp. 333–335:
    every compact subset of an analytic domain
    meets only finitely many components of the
    original analytic set. Actual translations and the
    existing compact local-component cover prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SetGermUP SetGermContinuousPreimage FiniteAnalyticVarietyUP
  AnalyticVarietyGermUP AnalyticSourceTranslation LocalComponentInverseTransport
  AnalyticVarietyLocalComponents CompactLocalComponentFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactComponents.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).

(** Source for [analytic_variety_germ_local_components]:
    the original analytic component family is locally
    finite at every centre, by 3.4.8(11),
    pp. 333–335. Translate the actual representative
    and transfer actual components by inverse translation. *)
Theorem analytic_variety_germ_local_components (S:set X) a:
  @is_analytic_variety_germ R X NX hNX a (@set_germ T a S) ->
  exists O:set X,@open T O /\O a /\
    finite_set (@connected_component T S @` (S `&` O)).
Proof.
move=>[U [H [haU [hH hGerm]]]].
pose u:=fun x:T=>(a+x:T).
pose v:=fun x:T=>(x-a:T).
have hU:continuous u:=@real_norm_metric_translate_continuous R X NX hNX a.
have hV:continuous v.
  have hSame:v = (fun x:T=>(-a+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hCentre:u 0 = a by rewrite /u addr0.
have hVU:cancel u v by move=>x;rewrite /u /v addrAC subrr add0r.
have hUV:cancel v u by move=>x;rewrite /u /v addrC subrK.
have hTranslatedVariety:=@finite_analytic_variety_source_translation R X NX hNX U H a hH.
have hTranslatedGerm:=@set_germ_continuous_preimage_equality T T u 0 a H S hU hCentre hGerm.
have hAtOrigin:@is_analytic_variety_germ R X NX hNX 0 (@set_germ T 0 (u @^-1` S)).
  exists (u @^-1` U),(u @^-1` H);split.
  - change (U (a+0));by rewrite addr0.
  - by split.
have [O [hO [hO0 hFinite]]]:=analytic_variety_germ_origin_local_components hAtOrigin.
exists (v @^-1` O);split;first exact:(@open_comp T T v O (fun x _=>hV x) hO).
split;first by change (O (a-a));rewrite subrr.
exact:(@local_component_inverse_transport T T u v S O hU hV hVU hUV hFinite).
Qed.

(** Source for [analytic_set_compact_component_finiteness]:
    the compact-component assertion in 3.4.5, p. 321,
    formerly a forward obligation to 3.4.8(11).
    The original analytic set is only locally analytic;
    neither global finite equations nor component finiteness
    are added as hypotheses. *)
Theorem analytic_set_compact_component_finiteness (U S K:set X):
  @is_analytic_set_in R X NX hNX U S ->@compact T K ->K `<=` U ->
  finite_set (@connected_component T S @` (S `&` K)).
Proof.
move=>hAnalytic hCompact hKU.
apply:(@compact_local_component_finiteness T S K hCompact)=>a ha.
exact:analytic_variety_germ_local_components (hAnalytic a (hKU a ha)).
Qed.
End CompactComponents.
