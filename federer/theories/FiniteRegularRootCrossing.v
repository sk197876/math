(** Federer (1969), 3.2.6, p. 246: the signed
    number of crossings of a regular finite level fibre
    depends only on the endpoint levels. The induction
    removes the first ordered root and uses continuity on
    the preceding root-free interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology normedtype lra.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP RealDerivativeCrossingSign ContinuousRootFreeSign.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_root_tail_head_bounds]: supporting
    ordered-root gap in the finite-fibre observation of
    Federer 3.2.6, p. 246. The right endpoint is
    used as a sentinel only when the root tail is empty. *)
Lemma real_root_tail_head_bounds (R:realType) (x b:R) (s:seq R):
  pairwise <%O s -> (forall t,t \in s -> x<t /\ t<b) -> x<b ->
  x<head b s /\ head b s<=b /\ forall t,t \in s -> head b s<=t.
Proof.
case:s=>[|z rest] hPair hBounds hxb.
- split; first exact hxb.
  split; first exact:lexx.
  by move=>t; rewrite in_nil.
- have hz:z \in z::rest by rewrite in_cons eqxx.
  have [hxz hzb]:=hBounds z hz.
  split; first exact hxz; split; first exact:ltW hzb.
  move=>t; rewrite in_cons=>/orP[/eqP ->|ht]; first exact:lexx.
  move/andP:hPair=>[hAll _].
  exact:ltW ((allP hAll) t ht).
Qed.

(** Source for [finite_regular_root_signed_crossing]: the
    finite-fibre observation in the proof of Federer 3.2.6,
    p. 246. Twice the sum of derivative signs is the
    final level sign minus the initial level sign. Endpoints
    need not have different values; all roots lie strictly
    between them and carry actual nonzero derivatives. *)
Theorem finite_regular_root_signed_crossing (R:realType) (f D:R->R) y
    (roots:seq R):
  continuous (f:real_line_metric R->real_line_metric R) ->
  forall a b:R,a<b -> pairwise <%O roots ->
  (forall t,t \in roots -> a<t /\ t<b) ->
  (forall t,a<=t -> t<=b -> (f t=y <-> t \in roots)) ->
  (forall t,t \in roots -> has_real_curve_derivative f t (D t) /\ D t!=0) ->
  2*\sum_(t<-roots) Num.sg (D t)=Num.sg (f b-y)-Num.sg (f a-y).
Proof.
move=>hCont; elim:roots=>[|x s ih] a b hab hOrder hInside hRoots hD.
- have hNo t:a<=t -> t<=b -> f t!=y.
    move=>hat htb; apply/eqP=>he; have hh:=(hRoots t hat htb).1 he; by rewrite in_nil in hh.
  have hSign:=@continuous_root_free_sign R f a b y (ltW hab) hCont hNo.
  by rewrite big_nil mulr0 hSign subrr.
move/andP:hOrder=>[hFirst hTail].
have hxMem:x \in x::s by rewrite in_cons eqxx.
have [hax hxb]:=hInside x hxMem.
have hfx:f x=y:=(hRoots x (ltW hax) (ltW hxb)).2 hxMem.
have [hDx hDx0]:=hD x hxMem.
have [d [hd hCross]]:=real_derivative_regular_crossing_sign hDx hDx0.
have hHead t:t \in s -> x<t by move/allP:hFirst=>h; exact:h.
pose z:=head b s.
have hTailBounds t:t \in s -> x<t /\ t<b.
  move=>ht; split; first exact (hHead t ht).
  have hMem:t \in x::s by rewrite in_cons ht orbT.
  exact (hInside t hMem).2.
have [hxz [hzb hzt]]:=@real_root_tail_head_bounds R x b s hTail hTailBounds hxb.
pose e:=Num.min d (z-x)/2.
have heMin:0<Num.min d (z-x) by rewrite lt_min hd subr_gt0.
have he:0<e by rewrite /e divr_gt0 // ltr0n.
have heBound:e<Num.min d (z-x) by rewrite /e; lra.
have hed:e<d.
  apply:lt_le_trans heBound _.
  by rewrite ge_min lexx.
have hez:e<z-x.
  apply:lt_le_trans heBound _.
  by rewrite ge_min lexx orbT.
pose c:=x+e.
have hxc:x<c by rewrite /c; lra.
have hcz:c<z by rewrite /c; lra.
have hcb:c<b:=lt_le_trans hcz hzb.
have hac:a<c:=lt_trans hax hxc.
have hct t:t \in s -> c<t:=fun ht=>lt_le_trans hcz (hzt t ht).
have heAbs:0<`|e|<d by rewrite (ger0_norm (ltW he)); apply/andP; split.
have hRight:Num.sg (f c-y)=Num.sg (D x).
  have hh:=hCross e heAbs.
  by rewrite hfx (gtr0_sg he) mul1r in hh.
pose l:=Num.min d (x-a)/2.
have hlMin:0<Num.min d (x-a) by rewrite lt_min hd subr_gt0.
have hl:0<l by rewrite /l divr_gt0 // ltr0n.
have hlBound:l<Num.min d (x-a) by rewrite /l; lra.
have hld:l<d.
  apply:lt_le_trans hlBound _.
  by rewrite ge_min lexx.
have hla:l<x-a.
  apply:lt_le_trans hlBound _.
  by rewrite ge_min lexx orbT.
pose t:=x-l.
have hat:a<t by rewrite /t; lra.
have htx:t<x by rewrite /t; lra.
have hlAbs:0<`|-l|<d by rewrite normrN (ger0_norm (ltW hl)); apply/andP; split.
have hLeft:Num.sg (f t-y)= -Num.sg (D x).
  have hh:=hCross (-l) hlAbs.
  have hlNeg:-l<0 by rewrite oppr_lt0.
  by rewrite hfx (ltr0_sg hlNeg) mulN1r in hh.
have hNo u:a<=u -> u<=t -> f u!=y.
  move=>hau hut; apply/eqP=>huy.
  have hub:u<=b:=le_trans hut (ltW (lt_trans htx hxb)).
  have hMem:=(hRoots u hau hub).1 huy.
  move:hMem; rewrite in_cons=>/orP[/eqP heq|hu].
  - subst u; by have:=lt_le_trans htx hut; rewrite ltxx.
  - have hxu:=hHead u hu; have hutx:=le_lt_trans hut htx; by have:=lt_trans hxu hutx; rewrite ltxx.
have hLeftEndpoint:Num.sg (f a-y)= -Num.sg (D x).
  have hh:=@continuous_root_free_sign R f a t y (ltW hat) hCont hNo.
  by rewrite hLeft in hh; exact (esym hh).
have hInsideTail u:u \in s -> c<u /\ u<b.
  move=>hu; split; first exact (hct u hu).
  have hMem:u \in x::s by rewrite in_cons hu orbT.
  exact (hInside u hMem).2.
have hRootsTail u:c<=u -> u<=b -> (f u=y <-> u \in s).
  move=>hcu hub; have hau:a<=u:=le_trans (ltW hac) hcu.
  split.
  - move=>huy; have hMem:=(hRoots u hau hub).1 huy.
    move:hMem; rewrite in_cons=>/orP[/eqP heq|hu]; last exact hu.
    have hcux:c<=x by rewrite -heq.
    by have:=lt_le_trans hxc hcux; rewrite ltxx.
  - move=>hu; apply:(hRoots u hau hub).2; by rewrite in_cons hu orbT.
have hDTail u:u \in s -> has_real_curve_derivative f u (D u) /\ D u!=0.
  move=>hu; apply:hD; by rewrite in_cons hu orbT.
have hSum:=ih c b hcb hTail hInsideTail hRootsTail hDTail.
rewrite big_cons.
rewrite hRight in hSum; rewrite hLeftEndpoint; lra.
Qed.
