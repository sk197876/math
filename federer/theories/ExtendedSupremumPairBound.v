(** Federer (1969), 4.1.12, p. 368: the
    single product-seminorm bound gives the exact sum
    of the two coordinate masses. Reuse the original
    least-upper-bound laws, without choosing maximizers. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal lra.
From Federer Require Import ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_supremum_pair_sum_bound]: a joint
    bound a+b<=c on two original value sets gives
    sup A+sup B<=c, supporting M(R)+M(S)<=F_K(T)
    in Federer 4.1.12, p. 368. Both sets contain
    zero; their finiteness follows from the joint bound. *)
Theorem extended_supremum_pair_sum_bound (R:realType) (A B:set R) s t c:
  A 0->B 0->is_extended_supremum A s->is_extended_supremum B t->
  (forall a,A a->forall b,B b->a+b<=c)->(s+t<=c%:E)%E.
Proof.
move=>hA0 hB0 hS hT hJoint.
have hS0:(0<=s)%E:=extended_supremum_upper hS hA0.
have hT0:(0<=t)%E:=extended_supremum_upper hT hB0.
have hSUpper:(s<=c%:E)%E.
  apply:(extended_supremum_least hS)=>a ha;rewrite lee_fin.
  have h:=hJoint a ha 0 hB0;by rewrite addr0 in h.
have hTUpper:(t<=c%:E)%E.
  apply:(extended_supremum_least hT)=>b hb;rewrite lee_fin.
  have h:=hJoint 0 hA0 b hb;by rewrite add0r in h.
have hSFinite:(s < +oo)%E:=le_lt_trans hSUpper (ltry c).
have hTFinite:(t < +oo)%E:=le_lt_trans hTUpper (ltry c).
have hSNumber:s \is a fin_num by rewrite (ge0_fin_numE hS0).
have hTNumber:t \is a fin_num by rewrite (ge0_fin_numE hT0).
pose a:=fine s;pose b:=fine t.
have hSValue:s=a%:E by rewrite /a fineK.
have hTValue:t=b%:E by rewrite /b fineK.
have hLast:(s<=(c-b)%:E)%E.
  apply:(extended_supremum_least hS)=>x hx;rewrite lee_fin.
  have hOther:(t<=(c-x)%:E)%E.
    apply:(extended_supremum_least hT)=>y hy;rewrite lee_fin.
    have h:=hJoint x hx y hy;lra.
  rewrite hTValue lee_fin in hOther;lra.
rewrite hSValue lee_fin in hLast.
rewrite hSValue hTValue -EFinD lee_fin;lra.
Qed.
