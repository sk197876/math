(** Federer (1969), 4.1.14, pp. 370–371: a family
    bounded and uniformly convergent on a larger compact
    index has the same original properties on every
    smaller compact index. No source neighbourhood,
    image map or smoothness hypothesis changes. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet CurrentSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [current_smooth_approximation_compact_mono]:
    restriction of the original K-only bounds, supporting
    compact-index independence in Federer 4.1.14,
    pp. 370–371. Empty compact indices are allowed. *)
Theorem current_smooth_approximation_compact_mono (R:realType) n nu
    (Z:set (R_n R n)) (V:set (R_n R nu))
    (K L:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) Z)
    (hKL:smooth_compact_carrier K `<=` smooth_compact_carrier L)
    (f:R_n R n->R_n R nu) (g:nat->R_n R n->R_n R nu):
  @is_current_smooth_approximation R n nu Z V L f g ->
  @is_current_smooth_approximation R n nu Z V K f g.
Proof.
move=>hG;constructor.
- exact:current_smooth_approximation_image hG.
- exact:current_smooth_approximation_class hG.
- have[c [hc hBound]]:=current_smooth_approximation_bound hG.
  exists c;split;first exact:hc.
  move=>i x hx;exact:hBound i x (hKL x hx).
- move=>epsilon hEpsilon.
  have[N hN]:=current_smooth_approximation_uniform hG hEpsilon.
  exists N=>i hNi x hx;exact:hN i hNi x (hKL x hx).
Qed.
