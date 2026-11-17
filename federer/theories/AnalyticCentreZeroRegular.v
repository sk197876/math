(** Federer (1969), 3.4.10, p. 337:
    every actual point of a zero-dimensional
    analytic set is regular. Translate the proved
    origin assertion and its exact manifold criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP AnalyticVarietyGermUP
  AnalyticSetLocalDepth AnalyticRegularLocusUP AnalyticRegularLocusSourceTranslation
  AnalyticOriginZeroRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_centre_zero_regular]: the
    zero-dimensional endpoint of 3.4.10, p. 337.
    The original centre is retained; the
    proof uses no negative measure degree. *)
Theorem analytic_centre_zero_regular (R:realType) n
    (U S L:set (R_n R n)) (a:R_n R n):
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->U a ->
  @is_analytic_variety_germ R (R_n R n) (inner_norm hB) hNX a (@set_germ T a S) ->
  (@analytic_set_local_depth R n S a<=0)%N ->
  @is_analytic_regular_locus R n 0 U S L ->S a ->L a.
Proof.
move=>hB hNX T hU haU hAnalytic hBound hL haS.
pose t:=fun x:T=>(a+x:T).
have hT:continuous t:=@real_norm_metric_translate_continuous R (R_n R n)
  (inner_norm hB) hNX a.
have hOpen:@open T (t @^-1` U):=@open_comp T T t U (fun x _=>hT x) hU.
have hZero:(t @^-1` U) 0 by change (U (a+0));rewrite addr0.
have hTranslated:=@analytic_set_translated_germ R n S a hAnalytic.
have hRegular:=@analytic_regular_locus_source_translation R n 0 U S L (-a) hL.
have hEq (A:set (R_n R n)):[set x|A (x-(-a))]=t @^-1` A.
  apply:funext=>x;change (A (x-(-a))=A (a+x));by rewrite opprK addrC.
rewrite !hEq in hRegular.
have hS0:(t @^-1` S) 0 by change (S (a+0));rewrite addr0.
have h:=@analytic_origin_zero_regular R n (t @^-1` U) (t @^-1` S) (t @^-1` L)
  hOpen hZero hTranslated hBound hRegular hS0.
change (L (a+0)) in h;by rewrite addr0 in h.
Qed.
