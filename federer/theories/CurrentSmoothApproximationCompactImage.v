(** Federer (1969), 4.1.14, p. 370: every allowed
    smooth approximation eventually sends K into every
    prescribed compact E whose interior contains f(K).
    This endpoint of the original affine-segment argument
    is independent of any current or measure. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct SmoothCompactSet CurrentSmoothApproximationUP
  CurrentSmoothApproximationSegments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_smooth_approximation_eventual_compact_image]:
    the eventual common compact target used throughout the
    approximation argument in Federer 4.1.14, pp. 370–371.
    Nonconvex E and empty K require no exceptional choice. *)
Theorem current_smooth_approximation_eventual_compact_image
    (R:realType) n nu (Z:set (R_n R n)) (V:set (R_n R nu))
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) Z)
    (f:R_n R n->R_n R nu) (g:nat->R_n R n->R_n R nu)
    (hG:@is_current_smooth_approximation R n nu Z V K f g)
    (hImage:forall x,Z x->V (f x))
    (hf:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R nu)) Z f)
    (E:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R nu)) V)
    (hInterior:forall x,smooth_compact_carrier K x->
      norm_domain_interior (inner_norm (@euclidean_inner_productP R nu))
        (smooth_compact_carrier E) (f x)):
  exists N:nat,forall i,(N<=i)%N->forall x,smooth_compact_carrier K x->
    smooth_compact_carrier E (g i x).
Proof.
have[N hN]:=@current_smooth_approximation_segments R n nu Z V K f g g hG hG
  hImage hf E hInterior.
exists N=>i hNi x hx.
have h:=hN i i hNi hNi x 0 hx (lexx 0) ler01.
by rewrite subr0 scale1r scale0r addr0 in h.
Qed.
