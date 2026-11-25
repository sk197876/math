(** Federer (1969), 4.1.2, p. 348: a compact test support
    admits one compact neighbourhood inside the arbitrary open domain.
    The same neighbourhood contains every sufficiently small convolution
    support, so the cutoff index can be chosen independently of epsilon. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP LinearBasis
  SmoothCompactSet SmoothCompactExhaustionUP SmoothCompactExhaustionSealed
  MetricOpenThickening MetricCompactNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_interior_thickening]: the common compact
    bound used when j is large and epsilon small in Federer 4.1.2,
    p. 348. It includes empty supports and zero-dimensional sources. *)
Theorem smooth_compact_interior_thickening (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x)
    (K:smooth_compact_set hNX U):
  exists r:R,0<r /\ exists C:smooth_compact_set hNX U,
    smooth_compact_carrier K `<=` smooth_compact_carrier C /\
    forall x z,smooth_compact_carrier K z ->NX (x-z)<=r ->smooth_compact_carrier C x.
Proof.
pose A:=@SmoothCompactExhaustion.value R X NX hNX n b hb U hU.
pose hA:=@SmoothCompactExhaustion.laws R X NX hNX n b hb U hU.
have[j [W [hW [hKW hWA]]]]:=smooth_compact_exhaustion_neighbourhood hA K.
have[r [hr hTube]]:=@compact_metric_open_thickening R (real_norm_metric_space hNX)
  (smooth_compact_carrier K) W (smooth_compact_is_compact K) hW hKW.
exists (r/2); split; first by rewrite divr_gt0 // ltr0n.
exists (A j); split; first by move=>x hx; exact:hWA x (hKW x hx).
move=>x z hz hDist; apply:hWA; apply:hTube.
exists z; first exact hz.
change (is_true (NX (z-x)<r)).
rewrite (real_seminorm_subtract hNX.1).
have hHalf:r/2<r by lra.
exact:le_lt_trans hDist hHalf.
Qed.
