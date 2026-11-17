(** Federer (1969), 3.4.10, p. 337:
    the original regular locus is relatively open
    in the original analytic set, directly by its
    local manifold definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric AnalyticSubmanifoldUP AnalyticRegularLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_regular_locus_open_form]: relative
    openness of the regular part of 3.4.10,
    p. 337. The original regular manifold witness
    at one point also works at every point
    of its intersection with S. *)
Theorem analytic_regular_locus_open_form (R:realType) n m (U S L:set (R_n R n)):
  is_analytic_regular_locus m U S L ->
  exists W:set (R_n R n),
    @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W /\
    W `<=` U /\L=S `&` W.
Proof.
move=>hL.
pose D:set (set (R_n R n)):=fun V=>
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) V /\
  V `<=` U /\@is_euclidean_analytic_submanifold R n m (S `&` V).
exists (\bigcup_(V in D) V);split.
- apply:bigcup_open=>V hV;exact:hV.1.
split.
- move=>x [V hV hx];exact:hV.2.1 x hx.
- apply/seteqP;split.
  + move=>a /hL [ha [V [hOpen [haV [hInside hManifold]]]]].
    split;first exact:ha.
    exists V;last exact:haV;by split=>//;split.
  + move=>a [ha [V [hOpen [hInside hManifold]] haV]].
    apply/hL;split;first exact:ha.
    exists V;by split=>//;split=>//;split.
Qed.
