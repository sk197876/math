(** Federer (1969), 3.2.2, p. 242: a sufficiently close
    source automorphism models the differential's vector lengths.
    Quantitative norm estimates express the neighbourhood used in
    the printed dense-family selection. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [linear_relative_margin_exists]: supporting the
    strict source-automorphism inequalities in Federer 3.2.2,
    p. 242. A positive t can satisfy a(1+t)<1<b(1-t)
    whenever 0<a<1<b. *)
Lemma linear_relative_margin_exists (R:realType) (a b:R) :
  0<a -> a<1 -> 1<b -> exists t:R,0<t /\ a*(1+t)<1 /\ 1<b*(1-t).
Proof.
move=>ha ha1 hb.
have hda:0<2*(a+1) by nra.
have hdb:0<2*(b+1) by nra.
pose t:=Num.min ((1-a)/(2*(a+1))) ((b-1)/(2*(b+1))).
have ht:0<t by rewrite /t lt_min; apply/andP; split; rewrite divr_gt0 // subr_gt0.
have hta:t*(2*(a+1))<=1-a.
  have hh:t<=(1-a)/(2*(a+1)) by rewrite /t ge_min lexx.
  by move:hh; rewrite ler_pdivlMr.
have htb:t*(2*(b+1))<=b-1.
  have hh:t<=(b-1)/(2*(b+1)) by rewrite /t ge_min lexx orbT.
  by move:hh; rewrite ler_pdivlMr.
exists t; split; first exact ht.
split; nra.
Qed.

(** Source for [linear_relative_model_neighbourhood]: supporting
    the dense S choice in Federer 3.2.2, p. 242. A bounded
    inverse to g gives a positive operator-error tolerance d;
    every s within that tolerance has a|sv|<=|gv|<=b|sv|.
    The positive tolerance exists also on the zero space. *)
Theorem linear_relative_model_neighbourhood (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (g h:Hom X X) a b p :
  cancel g h -> 0<=p -> (forall v,N (h v)<=p*N v) ->
  0<a -> a<1 -> 1<b ->
  exists d:R,0<d /\ forall s:Hom X X,
    (forall v,N (s v-g v)<=d*N v) ->
    forall v,a*N (s v)<=N (g v) /\ N (g v)<=b*N (s v).
Proof.
move=>hgh hp hInv ha ha1 hb.
have [t [ht [hat hbt]]]:=linear_relative_margin_exists ha ha1 hb.
have hp1:0<p+1 by nra.
pose d:=t/(p+1).
have hd:0<d by rewrite /d divr_gt0.
have hEq:d*(p+1)=t by rewrite /d divfK // gt_eqF.
have hdp:d* p<=t by nra.
exists d; split; first exact hd.
move=>s hErr v.
have hn:N v<=p*N (g v) by have hh:=hInv (g v); rewrite hgh in hh.
have hG:0<=N (g v):=real_seminorm_nonnegative hN.1 _.
have hS:0<=N (s v):=real_seminorm_nonnegative hN.1 _.
have hE:N (s v-g v)<=d* p*N (g v).
  apply:le_trans (hErr v) _; rewrite -mulrA; exact (ler_wpM2l (ltW hd) hn).
have hUpper:=real_seminorm_triangle hN.1 (s v-g v) (g v).
rewrite subrK in hUpper.
have hLower:=real_seminorm_triangle hN.1 (g v-s v) (s v).
rewrite subrK (real_seminorm_subtract hN.1 (g v) (s v)) in hLower.
have hU:N (s v)<=(1+t)*N (g v).
  have hmul:=ler_wpM2r hG hdp; nra.
have hL:(1-t)*N (g v)<=N (s v).
  have hmul:=ler_wpM2r hG hdp; nra.
split.
- have hmul:=ler_wpM2l (ltW ha) hU.
  have hcoef:=ler_wpM2r hG (ltW hat).
  nra.
- have hmul:=ler_wpM2l (ltW (lt_trans ltr01 hb)) hL.
  have hcoef:=ler_wpM2r hG (ltW hbt).
  nra.
Qed.
