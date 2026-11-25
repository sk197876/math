(** Federer (1969), 4.1.12, p. 369: a joint
    bound on separated test values bounds the product
    of their original dual suprema. This supporting
    least-upper-bound argument retains the ordinary
    partial-product domain and does not assume maximisers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal lra.
From Federer Require Import ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_supremum_product_bound]:
    the product of two nonnegative original suprema
    is bounded by c when every pair of real values
    has absolute product at most c, supporting
    Federer 4.1.12, p. 369. Zero and infinite
    suprema retain the original partial-product condition. *)
Theorem extended_supremum_product_bound (R:realType) (A B:set R) s t c:
  A 0->B 0->is_extended_supremum A s->is_extended_supremum B t->
  0<=c->mule_def s t->
  (forall a,A a->forall b,B b->`|a| * `|b|<=c)->(s*t<=c%:E)%E.
Proof.
move=>hA0 hB0 hS hT hc hDef hJoint.
have hS0:(0<=s)%E:=extended_supremum_upper hS hA0.
have hT0:(0<=t)%E:=extended_supremum_upper hT hB0.
case:(eqVneq s 0)=>hSzero;first by rewrite hSzero mul0e lee_fin.
case:(eqVneq t 0)=>hTzero;first by rewrite hTzero mule0 lee_fin.
have hAPos:exists a,A a /\0<a.
  case:(pselect (exists a,A a /\0<a))=>// hNo.
  have hUpper:(s<=0)%E.
    apply:(extended_supremum_least hS)=>a ha;rewrite lee_fin.
    case:(leP a 0)=>hSign;first by [].
    apply:False_ind;apply:hNo;exists a;by split.
  have hZero:s=0 by apply/eqP;rewrite eq_le hUpper hS0.
  by move:hSzero;rewrite hZero eqxx.
have hBPos:exists b,B b /\0<b.
  case:(pselect (exists b,B b /\0<b))=>// hNo.
  have hUpper:(t<=0)%E.
    apply:(extended_supremum_least hT)=>b hb;rewrite lee_fin.
    case:(leP b 0)=>hSign;first by [].
    apply:False_ind;apply:hNo;exists b;by split.
  have hZero:t=0 by apply/eqP;rewrite eq_le hUpper hT0.
  by move:hTzero;rewrite hZero eqxx.
have [a [ha hapos]]:=hAPos.
have [b [hb hbpos]]:=hBPos.
have hSBound:(s<=(c/b)%:E)%E.
  apply:(extended_supremum_least hS)=>x hx;rewrite lee_fin (ler_pdivlMr _ _ hbpos).
  apply:(le_trans (ler_wpM2r (ltW hbpos) (ler_norm x))).
  have h:=hJoint x hx b hb;by rewrite (ger0_norm (ltW hbpos)) in h.
have hTBound:(t<=(c/a)%:E)%E.
  apply:(extended_supremum_least hT)=>y hy;rewrite lee_fin (ler_pdivlMr _ _ hapos).
  apply:(le_trans (ler_wpM2r (ltW hapos) (ler_norm y))).
  have h:=hJoint a ha y hy;by rewrite (ger0_norm (ltW hapos)) mulrC in h.
have hSFinite:(s < +oo)%E:=le_lt_trans hSBound (ltry _).
have hTFinite:(t < +oo)%E:=le_lt_trans hTBound (ltry _).
have hSNumber:s \is a fin_num by rewrite (ge0_fin_numE hS0).
have hTNumber:t \is a fin_num by rewrite (ge0_fin_numE hT0).
pose u:=fine s;pose v:=fine t.
have hs:s=u%:E by rewrite /u fineK.
have ht:t=v%:E by rewrite /v fineK.
have hv:0<v.
  have h:=extended_supremum_upper hT hb;rewrite ht lee_fin in h.
  exact:lt_le_trans hbpos h.
have hLast:(s<=(c/v)%:E)%E.
  apply:(extended_supremum_least hS)=>x hx;rewrite lee_fin (ler_pdivlMr _ _ hv).
  case:(leP x 0)=>hSign.
  - exact:le_trans (mulr_le0_ge0 hSign (ltW hv)) hc.
  - have hOther:(t<=(c/x)%:E)%E.
      apply:(extended_supremum_least hT)=>y hy;rewrite lee_fin (ler_pdivlMr _ _ hSign).
      apply:(le_trans (ler_wpM2r (ltW hSign) (ler_norm y))).
      have h:=hJoint x hx y hy;by rewrite (ger0_norm (ltW hSign)) mulrC in h.
    rewrite ht lee_fin (ler_pdivlMr _ _ hSign) in hOther.
    by rewrite mulrC in hOther.
rewrite hs lee_fin (ler_pdivlMr _ _ hv) in hLast.
by rewrite hs ht -EFinM lee_fin.
Qed.
