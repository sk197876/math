(** Federer (1969), 2.5.7, p. 99: the residual functional is a difference of
    two increasing-continuous functionals. This elementary scalar sequence
    lemma supports its ordinary continuity, without assuming that the
    difference is monotone. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_difference_order_limit]: supporting scalar difference
    limit for the residual Daniell functional in Federer 2.5.7, p. 99 Both
    limits are finite, so no subtraction of infinities occurs. *)
Lemma real_difference_order_limit (R : realType) (u v : nat -> R) (a b : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (v n)%:E) b%:E ->
  extended_order_limit (fun n => (u n-v n)%:E) (a-b)%:E.
Proof.
move=> hu hv; apply: real_error_extended_order_limit=> e he.
have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [K hK] := @extended_finite_order_limit_error R u a (e/2)%R hu he2.
have [L hL] := @extended_finite_order_limit_error R v b (e/2)%R hv he2.
exists (maxn K L)=> n hn.
have hKn := leq_trans (leq_maxl K L) hn.
have hLn := leq_trans (leq_maxr K L) hn.
have heq : (u n-v n-(a-b)=(u n-a)-(v n-b))%R.
  rewrite !opprB [LHS]addrACA [RHS]addrACA.
  exact: (congr1 (fun t : R => (u n+b+t)%R) (addrC (-v n)%R (-a)%R)).
rewrite heq.
apply: le_lt_trans (ler_normB (u n-a)%R (v n-b)%R) _.
have hh := ltrD (hK n hKn) (hL n hLn).
by rewrite -splitr in hh.
Qed.
