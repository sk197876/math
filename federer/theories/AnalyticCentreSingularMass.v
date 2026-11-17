(** Federer (1969), 3.4.10, p. 337:
    the original nonregular part has locally finite
    H^(m-1) mass at every source centre.
    Reuse the origin theorem, the exact regular-locus
    translation and Hausdorff isometry invariance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness SetGermUP
  AnalyticVarietyGermUP AnalyticSetLocalDepth AnalyticRegularLocusUP
  AnalyticRegularLocusSourceTranslation AnalyticOriginSingularMass
  HausdorffLocalMassTranslation HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_centre_singular_positive_mass]: the
    local positive-dimensional singular-part bound in
    3.4.10, p. 337, at the
    actual original centre. All regular-locus criteria
    and analytic germs are transported by proved equations. *)
Theorem analytic_centre_singular_positive_mass (R:realType) n
    (U S L:set (R_n R n)) (a:R_n R n) u:
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->U a ->
  @is_analytic_variety_germ R (R_n R n) (inner_norm hB) hNX a (@set_germ T a S) ->
  (@analytic_set_local_depth R n S a<=u.+1)%N ->
  @is_analytic_regular_locus R n u.+1 U S L ->
  exists W:set (R_n R n),@open T W /\W a /\
    (@hausdorff_measure R (inner_metric_space hB) u ((S `\` L) `&` W)< +oo)%E.
Proof.
move=>hB hNX T hU haU hAnalytic hBound hL.
pose t:=fun x:T=>(a+x:T).
have hT:continuous t:=@real_norm_metric_translate_continuous R (R_n R n)
  (inner_norm hB) hNX a.
have hOpen:@open T (t @^-1` U):=@open_comp T T t U (fun x _=>hT x) hU.
have hZero:(t @^-1` U) 0 by change (U (a+0));rewrite addr0.
have hTranslated:=@analytic_set_translated_germ R n S a hAnalytic.
have hRegular:=@analytic_regular_locus_source_translation R n u.+1 U S L (-a) hL.
have hEq (A:set (R_n R n)):[set x|A (x-(-a))]=t @^-1` A.
  apply:funext=>x;change (A (x-(-a))=A (a+x));by rewrite opprK addrC.
rewrite !hEq in hRegular.
have [O [hO [hO0 [hOU hMass]]]]:=@analytic_origin_singular_positive_mass R n
  (t @^-1` U) (t @^-1` S) (t @^-1` L) u hOpen hZero hTranslated hBound hRegular.
apply:(@hausdorff_local_mass_translation R n (S `\` L) a u).
exists O;split;first exact:hO.
split;first exact:hO0.
exact:hMass.
Qed.
