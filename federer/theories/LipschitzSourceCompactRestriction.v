(** Federer (1969), 4.1.24, p. 380: preserve an
    original compact source while restricting a Lipschitz
    image witness over a target neighbourhood. The composite
    with a map Lipschitz on that neighbourhood is globally
    Lipschitz on the derived open source. This retains
    the printed source-map condition rather than replacing
    it by local Lipschitz regularity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormOpenPreimage InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP LipschitzBasic
  MetricLipschitzComposition SmoothCompactSet OpenLocalLipschitzCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_source_compact_neighbourhood_restriction]:
    the source restriction used for the locally Lipschitz
    target-image inclusion in 4.1.24, p. 380. The
    same original compact C remains admissible; neither
    its dimension nor its carrier is replaced. *)
Theorem lipschitz_source_compact_neighbourhood_restriction
    (R:realType) d n nu
    (Z:set (R_n R d))
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R d)) Z x)
    (C:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) Z)
    (W:set (R_n R n))
    (hW:forall y,W y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W y)
    (f:R_n R d->R_n R n) (g:R_n R n->R_n R nu):
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f->
  @is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) W g->
  (forall x,smooth_compact_carrier C x->W (f x))->
  exists A:set (R_n R d),
    (forall x,A x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R d)) A x) /\
    smooth_compact_carrier C `<=` A /\A `<=` Z /\
    (forall x,A x->W (f x)) /\
    @is_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) A
      (fun x=>g (f x)).
Proof.
move=>hF hG hCW.
pose X:=R_n R d;pose Y:=R_n R n;pose V:=R_n R nu.
pose NX:=inner_norm (@euclidean_inner_productP R d).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose NV:=inner_norm (@euclidean_inner_productP R nu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R d).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R nu).
pose A:set X:=[set x|Z x /\W (f x)].
have hClass:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY Z f hZ
  (@metric_lipschitz_is_local R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) Z f hF).
have hWOpen:@open (real_norm_metric_space hNY) W.
  rewrite openE=>y hy;exact:(@norm_domain_interior_neighbourhood R Y NY hNY W y).1
    (@hW y hy).
have hAOpen:@open (real_norm_metric_space hNX) A.
  exact:(@norm_class_zero_open_preimage R X Y NX NY hNX hNY Z W f hClass hWOpen).
have hA:forall x,A x->norm_domain_interior NX A x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX A x).2.
  exact:open_nbhs_nbhs (conj hAOpen hx).
exists A;split;first exact:hA.
split.
- move=>x hx;exact:conj (smooth_compact_in_domain C x hx) (hCW x hx).
- split;first by move=>x hx;exact:hx.1.
  split;first by move=>x hx;exact:hx.2.
  have[L [hL hFBound]]:=hF;have[M [hM hGBound]]:=hG.
  exists (M*L);split;first exact:mulr_gt0 hM hL.
  apply:(@metric_lipschitz_composition_bound R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY)
    (real_norm_metric_space hNV) A W f g L M (fun x hx=>hx.2) _ hGBound).
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) Z A f L (fun x hx=>hx.1) hFBound).
Qed.
