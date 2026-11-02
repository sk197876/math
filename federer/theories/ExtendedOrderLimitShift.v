(** Federer (1969), 2.4.17, p. 90: discarding finitely many exponents when
    using a summable bracket. These supporting sequence-tail rules are
    elementary order-topology background. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ereal_scope.

(** Source for [extended_order_limit_shift]: supporting passage to a tail in
    the exponent-continuity proof of Federer 2.4.17, p. 90 *)
Lemma extended_order_limit_shift (R : realType) (u : nat -> \bar R) l k :
  extended_order_limit u l -> extended_order_limit (fun n => u (k+n)%N) l.
Proof.
move=> [hlo hup]; split=> b hb.
- have [j hj] := hlo b hb; exists j=> n hn; exact: hj _ (leq_trans hn (leq_addl k n)).
- have [j hj] := hup b hb; exists j=> n hn; exact: hj _ (leq_trans hn (leq_addl k n)).
Qed.

(** Source for [extended_order_limit_of_shift]: supporting removal of a
    finite prefix in the continuity argument of Federer 2.4.17, p. 90 *)
Lemma extended_order_limit_of_shift (R : realType) (u : nat -> \bar R) l k :
  extended_order_limit (fun n => u (k+n)%N) l -> extended_order_limit u l.
Proof.
move=> [hlo hup]; split=> b hb.
- have [j hj] := hlo b hb; exists (k+j)%N=> n hn.
  have hkn : (k <= n)%N := leq_trans (leq_addr j k) hn.
  have hjn : (j <= n-k)%N by rewrite leq_subRL // addnC.
  have hh := hj _ hjn; by rewrite addnC subnK in hh.
- have [j hj] := hup b hb; exists (k+j)%N=> n hn.
  have hkn : (k <= n)%N := leq_trans (leq_addr j k) hn.
  have hjn : (j <= n-k)%N by rewrite leq_subRL // addnC.
  have hh := hj _ hjn; by rewrite addnC subnK in hh.
Qed.
