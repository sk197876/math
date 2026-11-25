(** Supporting convex lifting geometry for Federer (1969), 2.10.5(2), p.
    173, and 3.2.36, p. 272. Contract a source convex set toward a
    section-buffer centre. The contracted set admits section displacements
    smaller than the original buffer radius times the unused contraction
    factor. This follows directly from the segment definition of convexity
    in 1.7.13, p. 37; it is a supporting lemma, not a separately printed
    measure claim. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_contracted_section_buffer]:
    supporting absorption of small lifting errors
    in Federer 2.10.5(2), p. 173, and the
    continuity background 3.2.36, p. 272. The
    displacement lies in a proved section ball;
    no ambient interior of K is required. *)
Theorem convex_contracted_section_buffer (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (b y : R_n R n) (g : {linear R_n R m -> R_n R n}) (r s : R)
    (w : inner_metric_space (@euclidean_inner_productP R m)) :
  is_inner_convex K -> K y -> 0<s -> s<1 ->
  (forall u : inner_metric_space (@euclidean_inner_productP R m),
    mdist (0%R : inner_metric_space (@euclidean_inner_productP R m)) u<r -> K (b+g u)) ->
  mdist (0%R : inner_metric_space (@euclidean_inner_productP R m)) w<(1-s)*r ->
  K (((1-s)*:b+s*:y)+g w).
Proof.
move=> hK hy hs hs1 hbuffer hw.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose u : Y := (1-s)^-1*:w.
have hc : 0<1-s by rewrite subr_gt0.
have hcN : 1-s!=0 by rewrite gt_eqF.
have hu : mdist (0%R:Y) u<r.
  rewrite /u inner_metric_distanceE sub0r inner_normN inner_normZ ger0_norm;
    last by rewrite invr_ge0; exact: ltW hc.
  rewrite mulrC ltr_pdivrMr //.
  move: hw; by rewrite inner_metric_distanceE sub0r inner_normN mulrC.
have hh := hK (b+g u) y (hbuffer u hu) hy s (ltW hs) (ltW hs1).
have he : (1-s)*:g u=g w.
  by rewrite /u linearZ scalerA mulfV // scale1r.
rewrite scalerDr he addrAC in hh; exact hh.
Qed.
