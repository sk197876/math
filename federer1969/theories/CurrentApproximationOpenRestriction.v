(** Federer (1969), 4.1.14, p. 370: two source
    neighbourhoods can be compared on their intersection.
    Local Lipschitzness, smoothness and the original K-only
    approximation bounds persist on the smaller source.
    Use the exact derivative locality of 3.1.1, pp. 209–210. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentLipschitzCompactImage
  CurrentSmoothApproximationUP SmoothClassOpenRestriction
  CurrentMapDifferentialOpenRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [metric_local_lipschitz_domain_restriction]:
    restriction of the original locally Lipschitz map,
    supporting the source-neighbourhood comparison in Federer
    4.1.14, p. 370, by 2.2.7, p. 64. The smaller
    domain need not be open for this relative assertion. *)
Theorem metric_local_lipschitz_domain_restriction (R:realType)
    (X Y:metricType R) (U W:set X) (f:X->Y):
  W `<=` U ->@is_locally_metric_lipschitz R X Y U f ->
  @is_locally_metric_lipschitz R X Y W f.
Proof.
move=>hWU hLocal x hx.
have[O [hO [L [hL [hNonnegative hBound]]]]]:=hLocal x (hWU x hx).
exists O;split;first exact:hO.
exists L;split;first exact:hL.
split;first exact:hNonnegative.
move=>a b [hA hAO] [hB hBO].
exact:hBound a b (conj (hWU a hA) hAO) (conj (hWU b hB) hBO).
Qed.

(** Source for [current_smooth_approximation_open_restriction]:
    each original smooth sequence restricts to any smaller
    open neighbourhood containing K, Federer 4.1.14, p. 370.
    The same finite cap is kept only on K; the actual
    differential field is unchanged there. *)
Theorem current_smooth_approximation_open_restriction (R:realType) n nu
    (Z W:set (R_n R n)) (V:set (R_n R nu))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWZ:W `<=` Z)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) Z)
    (hKW:smooth_compact_carrier K `<=` W)
    (f:R_n R n->R_n R nu) (g:nat->R_n R n->R_n R nu):
  @is_current_smooth_approximation R n nu Z V K f g ->
  @is_current_smooth_approximation R n nu W V
    (@current_compact_index_in_open R n Z W K hKW) f g.
Proof.
move=>hG;constructor.
- move=>i x hx;exact:@current_smooth_approximation_image R n nu Z V K f g hG i x (hWZ x hx).
- move=>i;exact:(@smooth_class_open_restriction R (R_n R n) (R_n R nu)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R nu))
    Z W (g i) hWZ hW (current_smooth_approximation_class hG i)).
- have[L [hL hBound]]:=current_smooth_approximation_bound hG.
  exists L;split;first exact:hL.
  move=>i x hx.
  rewrite (@current_map_differential_open_restriction R n nu W Z hW hWZ
    (g i) (current_smooth_approximation_class hG i) x (hKW x hx)).
  exact:hBound i x hx.
- exact:current_smooth_approximation_uniform hG.
Qed.
