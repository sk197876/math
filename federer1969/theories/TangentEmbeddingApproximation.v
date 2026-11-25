(** Federer (1969), 3.1.21, p. 234: quantitative proof of
    the reverse tangent-image inclusion for a closed-range embedding. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  TangentConeUP TangentConeBasic TangentEmbeddingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_embedding_approximation]: supporting
    estimate in the reverse-inclusion proof of Federer 3.1.21,
    p. 234. The lower bound controls r|x-a| by |r(f(x)-f(a))|;
    the differentiability error therefore tends to zero. The
    statement gives witnesses rather than assuming convergence. *)
Theorem norm_tangent_embedding_approximation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) a (L:Hom X Y) c w :
  has_norm_differential NX NY A f a L -> 0<c ->
  (forall x,c*NX x<=NY (L x)) ->
  norm_inverse_continuous_on_set NX NY S f a ->
  norm_tangent_cone NY (f @` S) (f a) w ->
  forall e d:R,0<e -> 0<d -> exists (x:X) (r:R),
    S x /\ 0<r /\ NX (x-a)<e /\ NY (L (r*:(x-a))-w)<d.
Proof.
move=>hf hc hlow hinv hw e d he hd.
have hnw:=real_seminorm_nonnegative hNY.1 w.
pose t:=Num.min (c/2) (c*d/(8*(NY w+1))).
have hc2:0<c/2 by rewrite divr_gt0 // ltr0n.
have hnw1:0<NY w+1 by lra.
have h8:0<(8:R) by lra.
have hden:0<8*(NY w+1):=mulr_gt0 h8 hnw1.
have hnum:0<c*d:=mulr_gt0 hc hd.
have hcd:0<c*d/(8*(NY w+1)):=divr_gt0 hnum hden.
have ht:0<t by rewrite /t lt_min hc2 hcd.
have ht1:t*2<=c.
  have hh:=real_minimum_left_bound (c/2) (c*d/(8*(NY w+1))).
  by rewrite ler_pdivlMr ?ltr0n in hh.
have ht2:t*(8*(NY w+1))<=c*d.
  have hh:=real_minimum_right_bound (c/2) (c*d/(8*(NY w+1))).
  rewrite ler_pdivlMr in hh; first exact hh.
  apply: mulr_gt0; lra.
have [ra [hra hA]]:=norm_differential_interior hf.
have [rd [hrd hrem]]:=norm_differential_remainder hf ht.
pose q:=Num.min e (Num.min ra rd).
have hq:0<q by rewrite /q !lt_min he hra hrd.
have [ri [hri hinvri]]:=hinv q hq.
pose s:=Num.min 1 (d/4).
have hs:0<s by rewrite /s lt_min ltr01 divr_gt0 // ltr0n.
have hri':0<ri:=hri.
have [y [r [[x hx <-] [hr [hfx hry]]]]]:=
  (@norm_tangent_two_radii R Y NY (f @` S) (f a) w).1 hw ri s hri hs.
pose h:=x-a.
have hsmall:NX h<q:=hinvri x hx hfx.
have hhe:NX h<e:=lt_le_trans hsmall (real_minimum_left_bound e (Num.min ra rd)).
have hha:NX h<ra.
  exact (lt_le_trans hsmall (le_trans (real_minimum_right_bound e (Num.min ra rd)) (real_minimum_left_bound ra rd))).
have hhd:NX h<rd.
  exact (lt_le_trans hsmall (le_trans (real_minimum_right_bound e (Num.min ra rd)) (real_minimum_right_bound ra rd))).
have hshift:a+h=x by rewrite /h addrC subrK.
have hAx:A (a+h):=hA h hha.
have hremx:=hrem h hAx hhd; rewrite hshift in hremx.
have htri:NY (L h)<=NY (f x-f a)+NY (f x-f a-L h).
  have heq:L h=(f x-f a)+ -(f x-f a-L h) by rewrite opprB addrC subrK.
  rewrite {1}heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  by rewrite (real_seminorm_negate hNY.1).
have hnx:=real_seminorm_nonnegative hNX.1 h.
have hnh:c*NX h<=2*NY (f x-f a).
  have hh:=hlow h; nra.
have hry0:=real_seminorm_nonnegative hNY.1 (r*:(f x-f a)-w).
have hrs1:NY (r*:(f x-f a)-w)<1:=lt_le_trans hry (real_minimum_left_bound 1 (d/4)).
have hrsd:NY (r*:(f x-f a)-w)<d/4:=lt_le_trans hry (real_minimum_right_bound 1 (d/4)).
have hrf:NY (r*:(f x-f a))<=NY (r*:(f x-f a)-w)+NY w.
  have hh:=real_seminorm_triangle hNY.1 (r*:(f x-f a)-w) w.
  by rewrite subrK in hh.
have hrfE:NY (r*:(f x-f a))=r*NY (f x-f a).
  by rewrite (real_seminorm_scale hNY.1) (ger0_norm (ltW hr)).
have hrnx:c*(r*NX h)<=2*(NY w+1).
  have hh:=ler_wpM2l (ltW hr) hnh; nra.
have hre:NY (r*:(f x-f a-L h))<=t*(r*NX h).
  rewrite (real_seminorm_scale hNY.1) (ger0_norm (ltW hr)).
  have hh:=ler_wpM2l (ltW hr) hremx; nra.
have herr:NY (L (r*:h)-w)<=NY (r*:(f x-f a-L h))+NY (r*:(f x-f a)-w).
  have heq:L (r*:h)-w= -(r*:(f x-f a-L h))+(r*:(f x-f a)-w).
    rewrite [r*:(f x-f a-L h)]scalerBr linearZ /= opprB.
    by rewrite addrA subrK.
  rewrite {1}heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  by rewrite (real_seminorm_negate hNY.1).
exists x,r; split=>//; split=>//; split=>//.
change (NY (L (r*:h)-w)<d).
nra.
Qed.
