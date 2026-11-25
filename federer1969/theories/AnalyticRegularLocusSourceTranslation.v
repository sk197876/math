(** Federer (1969), 3.4.10, p. 337:
    the original regular-locus criterion is preserved
    by actual source translation. Use the
    proved translation of analytic manifold charts
    in both directions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticSubmanifoldUP
  AnalyticRegularLocusUP AnalyticSubmanifoldSourceTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_regular_locus_source_translation]: the
    same original regular points in translated
    coordinates, needed for the all-centre singular-part
    assertions of 3.4.10, p. 337.
    Neighbourhoods, domain containment and analytic manifold
    dimension are all retained explicitly. *)
Theorem analytic_regular_locus_source_translation (R:realType) n m
    (U S L:set (R_n R n)) (c:R_n R n):
  @is_analytic_regular_locus R n m U S L ->
  @is_analytic_regular_locus R n m [set x|U (x-c)] [set x|S (x-c)] [set x|L (x-c)].
Proof.
move=>hL.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose u:=fun x:T=>(x-c:T).
pose v:=fun x:T=>(x+c:T).
have hU:continuous u.
  have hSame:u=(fun x:T=>(-c+x:T)) by apply:funext=>x;rewrite /u addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hV:continuous v.
  have hSame:v=(fun x:T=>(c+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hUV:cancel v u by move=>x;rewrite /u /v addrK.
have hVU:cancel u v by move=>x;rewrite /u /v subrK.
move=>b;split.
- move/(hL (u b))=>[hbS [V [hOpen [hbV [hInside hManifold]]]]].
  split;first exact:hbS.
  exists (u @^-1` V);split;first exact:(@open_comp T T u V (fun x _=>hU x) hOpen).
  split;first exact:hbV.
  split;first by move=>x hx;exact:hInside (u x) hx.
  exact:(@analytic_submanifold_source_translation R n m (S `&` V) c hManifold).
- move=>[hbS [W [hOpen [hbW [hInside hManifold]]]]].
  apply/(hL (u b));split;first exact:hbS.
  exists (v @^-1` W);split;first exact:(@open_comp T T v W (fun x _=>hV x) hOpen).
  split;first by change (W (v (u b)));rewrite hVU.
  split.
  + move=>x hx;have h:=hInside (v x) hx.
    change (U (u (v x))) in h;by rewrite hUV in h.
  + have hOriginal:=@analytic_submanifold_source_translation R n m
      ((u @^-1` S) `&` W) (-c) hManifold.
    have hSame:[set x|((u @^-1` S) `&` W) (x-(-c))]=S `&` (v @^-1` W).
      apply:funext=>x.
      change ((S ((x-(-c))-c) /\W (x-(-c)))=(S x /\W (x+c))).
      by rewrite opprK addrK.
    by rewrite hSame in hOriginal.
Qed.
