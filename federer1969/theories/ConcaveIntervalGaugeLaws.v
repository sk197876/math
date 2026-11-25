(** Federer (1969), 2.10.28, pp. 191–193: consequences of the abstract
    concave-gauge laws. The decreasing-increment inequality is used
    explicitly on p. 192 in proof (1), and strict sublinear dilation gives
    the separation of the children in (4). *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ConcaveIntervalGaugeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [concave_interval_gauge_nonnegative]:
    supporting nonnegative costs in 2.10.28,
    p. 191; increasing h and h(0)=0
    imply nonnegativity on its specified domain. *)
Lemma concave_interval_gauge_nonnegative (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) x : 0<=x -> 0<=h x.
Proof.
move=> hx; have hi := @interval_gauge_increasing R h hg 0 x (lexx 0) hx.
by rewrite (interval_gauge_zero hg) in hi.
Qed.

(** Source for [concave_interval_gauge_concavity]: supporting weak concavity
    used in proofs (1) and (4) of 2.10.28, pp. 192–193. Include equal inputs
    and weights zero or one *)
Lemma concave_interval_gauge_concavity (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) a b t :
  0<=a -> 0<=b -> 0<=t -> t<=1 ->
  (1-t)*h a+t*h b<=h ((1-t)*a+t*b).
Proof.
move=> ha hb ht ht1; case: (eqVneq a b)=> [->|hab].
  have he : (1-t)*b+t*b=b by rewrite -mulrDl subrK mul1r.
  have hh : (1-t)*h b+t*h b=h b by rewrite -mulrDl subrK mul1r.
  by rewrite he hh.
case: (eqVneq t 0)=> [->|ht0]; first by rewrite subr0 !mul1r !mul0r !addr0.
case: (eqVneq t 1)=> [->|htone]; first by rewrite subrr !mul0r !mul1r !add0r.
have htp : 0<t by rewrite lt_neqAle eq_sym ht0 ht.
have htl : t<1 by rewrite lt_neqAle htone ht1.
exact: ltW (interval_gauge_strict_concavity hg ha hb hab htp htl).
Qed.

(** Source for [concave_interval_gauge_strictly_increasing]: supporting
    strict growth in 2.10.28(4), p. 192. Strict concavity and the given weak
    monotonicity imply strict growth even at zero. *)
Lemma concave_interval_gauge_strictly_increasing (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) a b : 0<=a -> a<b -> h a<h b.
Proof.
move=> ha hab.
pose c := (b+(b-a)).
have hc : 0<=c by rewrite /c; lra.
have hac : a!=c by apply/negP=> /eqP he; rewrite /c in he; lra.
have hmid : (1-(2:R)^-1)*a+(2:R)^-1*c=b by rewrite /c; lra.
have hw0 : (0<(2:R)^-1) by rewrite invr_gt0 ltr0n.
have hw1 : ((2:R)^-1<1) by lra.
have hs := interval_gauge_strict_concavity hg ha hc hac hw0 hw1.
rewrite hmid in hs.
have hacle : a<=c by rewrite /c; lra.
have hmon := @interval_gauge_increasing R h hg a c ha hacle.
lra.
Qed.

(** Source for [concave_interval_gauge_decreasing_increments]: direct
    inequality h(a+r)-h(a)>=h(b+r)-h(b) in the proof of 2.10.28(1), p. 192,
    for 0<=a<=b and r>=0. *)
Lemma concave_interval_gauge_decreasing_increments (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) a b r :
  0<=a -> a<=b -> 0<=r -> h (b+r)-h b<=h (a+r)-h a.
Proof.
move=> ha hab hr.
pose s := b-a.
pose d := s+r.
have hs : 0<=s by rewrite /s subr_ge0.
have hd : 0<=d by rewrite /d; exact: addr_ge0.
case: (eqVneq d 0)=> [hd0|hd0].
  have heq : a=b by rewrite /d /s in hd0; lra.
  by rewrite heq.
have hdp : 0<d by rewrite lt_neqAle eq_sym hd0 hd.
pose t := s/d.
pose u := r/d.
have ht : 0<=t by rewrite /t divr_ge0 //; exact: ltW hdp.
have hu : 0<=u by rewrite /u divr_ge0 //; exact: ltW hdp.
have hsum : t+u = 1 by rewrite /t /u -mulrDl -/d divff.
have ht1 : t<=1 by lra.
have hu1 : u<=1 by lra.
have hbig : 0<=b+r by lra.
have hdiff : b+r-a=d by rewrite /d /s; lra.
have hpoint (v : R) : (1-v)*a+v*(b+r)=a+v*(b+r-a).
  by rewrite mulrBl mul1r mulrBr; lra.
have hbpoint : (1-t)*a+t*(b+r)=b.
  rewrite hpoint hdiff /t divfK // /s; lra.
have harpoint : (1-u)*a+u*(b+r)=a+r.
  by rewrite hpoint hdiff /u divfK.
have h1 := concave_interval_gauge_concavity hg ha hbig ht ht1.
have h2 := concave_interval_gauge_concavity hg ha hbig hu hu1.
rewrite hbpoint in h1; rewrite harpoint in h2.
have hsumcost : (1-t)*h a+t*h (b+r)+((1-u)*h a+u*h (b+r))=h a+h (b+r).
  have hueq : u = (1-t) by lra.
  rewrite hueq; lra.
have hh := lerD h1 h2; rewrite hsumcost in hh; lra.
Qed.

(** Source for [concave_interval_gauge_subadditive]:
    supporting subadditivity of interval costs in
    2.10.28(1), pp. 191–192, obtained by
    taking the smaller starting point zero in
    its decreasing-increment inequality. *)
Lemma concave_interval_gauge_subadditive (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) a b : 0<=a -> 0<=b -> h (a+b)<=h a+h b.
Proof.
move=> ha hb.
have hh := concave_interval_gauge_decreasing_increments hg (lexx (0:R)) ha hb.
rewrite add0r (interval_gauge_zero hg) subr0 in hh; lra.
Qed.

(** Source for [concave_interval_gauge_strict_dilation]: supporting
    separation of the equal-cost child intervals in 2.10.28(4), pp. 192–193
    Strict concavity between zero and tau*t gives h(tau*t)<tau*h(t) for
    tau>1,t>0. *)
Lemma concave_interval_gauge_strict_dilation (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) t u :
  0<t -> 1<u -> h (u*t)<u*h t.
Proof.
move=> ht hu.
have hu0 : 0<u by lra.
have huN : u!=0 by rewrite gt_eqF.
have hui : 0<u^-1 by rewrite invr_gt0.
have hui1 : u^-1<1 by rewrite invf_lt1.
have hut : 0<u*t := mulr_gt0 hu0 ht.
have hne : (0:R)!=u*t by rewrite eq_sym gt_eqF.
have hh := @interval_gauge_strict_concavity R h hg 0 (u*t) u^-1
  (lexx 0) (ltW hut) hne hui hui1.
rewrite (interval_gauge_zero hg) !mulr0 !add0r mulrA mulVf // mul1r in hh.
have hs : u*(u^-1*h (u*t))<u*h t by rewrite (ltr_pM2l hu0).
by rewrite mulrA mulfV // mul1r in hs.
Qed.
