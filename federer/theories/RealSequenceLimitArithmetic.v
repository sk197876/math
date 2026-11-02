(** Federer (1969), 2.5.3, p. 95, final paragraph: the lattice of convergent
    real sequences and its limit functional. These supporting finite-limit
    laws use the earlier order-limit epsilon criterion and real arithmetic. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealErrorOrderLimit RealScalarOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_sequence_limit_add]: elementary addition limit
    supporting the lattice and functional in Federer 2.5.3, p. 95 *)
Lemma real_sequence_limit_add (R : realType) (u v : nat -> R) (a b : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (v n)%:E) b%:E ->
  extended_order_limit (fun n => (u n+v n)%R%:E) (a+b)%R%:E.
Proof.
move=> hu hv; apply: real_error_extended_order_limit=> e he.
have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [N hN] := extended_finite_order_limit_error hu he2.
have [M hM] := extended_finite_order_limit_error hv he2.
exists (maxn N M)=> n hn.
have hnN := leq_trans (leq_maxl N M) hn.
have hnM := leq_trans (leq_maxr N M) hn.
have herr := ltrD (hN n hnN) (hM n hnM); rewrite -splitr in herr.
rewrite opprD addrACA; exact: le_lt_trans (ler_normD _ _) herr.
Qed.

(** Source for [real_sequence_limit_subtract]: arbitrary difference limit
    supporting the convergent-sequence lattice of Federer 2.5.3, p. 95 This
    example is a vector space. *)
Lemma real_sequence_limit_subtract (R : realType) (u v : nat -> R) (a b : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (v n)%:E) b%:E ->
  extended_order_limit (fun n => (u n-v n)%R%:E) (a-b)%R%:E.
Proof.
move=> hu hv; have hn := @real_scalar_order_limit R v b (-1)%R hv.
have hs := @real_sequence_limit_add R u (fun n => (-1*v n)%R) a (-1*b)%R hu hn.
have he : (fun n => (u n+ -1*v n)%R%:E)=(fun n => (u n-v n)%R%:E).
  by apply: funext=> n; rewrite mulN1r.
by rewrite he mulN1r in hs.
Qed.

(** Source for [real_sequence_limit_absolute]: elementary absolute-value
    limit supporting minimum closure in Federer 2.5.3, p. 95 *)
Lemma real_sequence_limit_absolute (R : realType) (u : nat -> R) (a : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (`|u n|%R)%:E) (`|a|%R)%:E.
Proof.
move=> hu; apply: real_error_extended_order_limit=> e he.
have [N hN] := extended_finite_order_limit_error hu he.
exists N=> n hn; exact: le_lt_trans (ler_dist_dist _ _) (hN n hn).
Qed.

(** Source for [real_sequence_limit_minimum]: minimum closure supporting the
    exact lattice in Federer 2.5.3, p. 95 The formula min(a,b)=(a+b-|a-b|)/2
    reduces it to the preceding limits. *)
Lemma real_sequence_limit_minimum (R : realType) (u v : nat -> R) (a b : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (v n)%:E) b%:E ->
  extended_order_limit (fun n => (Order.min (u n) (v n))%:E) (Order.min a b)%:E.
Proof.
move=> hu hv.
have hs := real_sequence_limit_add hu hv.
have hd := real_sequence_limit_subtract hu hv.
have ha := real_sequence_limit_absolute hd.
have hb := real_sequence_limit_subtract hs ha.
have hc := @real_scalar_order_limit R _ _ (2^-1)%R hb.
have he : (fun n => (2^-1 * (u n+v n-`|u n-v n|))%R%:E)=
    (fun n => (Order.min (u n) (v n))%:E).
  by apply: funext=> n; rewrite minr_absE mulrC.
have he' : (2^-1 * (a+b-`|a-b|))%R=Order.min a b by rewrite minr_absE mulrC.
by rewrite he he' in hc.
Qed.
