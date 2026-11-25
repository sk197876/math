(** Federer (1969), 3.1.18, p. 229: open convex neighbourhoods and
    their inverse images under the coordinate projections. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerConvex
  NormConvexHullDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bounded_linear_preimage_interior]: a bounded
    linear inverse image of a neighbourhood is a neighbourhood,
    supporting the product domains in Federer 3.1.18, p. 229. *)
Lemma norm_bounded_linear_preimage_interior (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (L:Hom X Y)
    (B:Y->Prop) a : norm_bounded_linear NX NY L ->
  norm_domain_interior NY B (L a) ->
  norm_domain_interior NX (fun x=>B (L x)) a.
Proof.
move=>[C [hC hb]] [r [hr hball]].
have hden:0<C+1 by lra.
exists (r/(C+1)); split; first by rewrite divr_gt0.
move=>h hh.
have hmul:(C+1)*NX h<r by move: hh; rewrite ltr_pdivlMr // mulrC.
have hn:=real_seminorm_nonnegative hNX.1 h.
have hsmall:NY (L h)<r by apply: le_lt_trans (hb h) _; nra.
have he:=hball (L h) hsmall.
by rewrite linearD.
Qed.

(** Source for [norm_domain_intersection_interior]: finite intersections
    of neighbourhoods are neighbourhoods, supporting simultaneous rank
    and coordinate restrictions in Federer 3.1.18, pp. 229–230. *)
Lemma norm_domain_intersection_interior (R:realType) (X:lmodType R)
    (NX:X->R) (A B:X->Prop) a :
  norm_domain_interior NX A a -> norm_domain_interior NX B a ->
  norm_domain_interior NX (fun x=>A x /\ B x) a.
Proof.
move=>[r [hr hA]] [s [hs hB]].
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=>h; rewrite lt_min=>/andP [hhr hhs]; exact: conj (hA h hhr) (hB h hhs).
Qed.

(** Source for [norm_open_ball_convex]: open norm balls are convex,
    giving the convex V and W chosen in Federer 3.1.18, p. 229. *)
Lemma norm_open_ball_convex (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) c r :
  is_inner_convex (fun x=>NX (x-c)<r).
Proof.
move=>x y hx hy t ht ht1.
pose s:=Num.max (NX (x-c)) (NX (y-c)).
have hs:s<r by rewrite /s gt_max hx hy.
have hxs:NX (x-c)<=s by rewrite /s le_max lexx.
have hys:NX (y-c)<=s by rewrite /s le_max lexx orbT.
have hb:=@norm_ball_inner_convex R X NX hNX c s x y hxs hys t ht ht1.
exact: le_lt_trans hb hs.
Qed.
