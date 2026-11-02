(** Federer (1969), 2.4.9, p. 85: the limit g remains bounded by h, and
    2h-|fn-g| tends pointwise to 2h. These scalar supporting lemmas make the
    finite-value part of that argument explicit. Source context:
    MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit ExtendedRealLimitBounds RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_dominated_limit_bound]: supporting
    passage of the absolute bound to the pointwise limit in
    Federer 2.4.9, p. 85. *)
Lemma extended_dominated_limit_bound (R : realType) (u : nat -> \bar R) z h :
  extended_order_limit u z -> (forall n, `|u n| <= h) -> `|z| <= h.
Proof.
move=> hlim hb.
have hupper : z <= h.
  apply: (@extended_order_limit_upper_bound R u z h hlim)=> n.
  exact: le_trans (lee_abs (u n)) (hb n).
have hlower : -h <= z.
  apply: (@extended_order_limit_lower_bound R u z (-h) hlim)=> n.
  rewrite leeNl; apply: le_trans _ (hb n).
  by move: (lee_abs (-u n)); rewrite abseN.
have [hz|hz] := leP 0 z.
- by rewrite (gee0_abs hz).
- rewrite (lee0_abs (ltW hz)); by move: hlower; rewrite leeNl.
Qed.

(** Source for [extended_finite_dominated_values]: supporting
    finiteness of each dominated value and its limit in
    Federer 2.4.9, p. 85, wherever the summable
    dominator has finite value. *)
Lemma extended_finite_dominated_values (R : realType) (u : nat -> \bar R) z (h : R) :
  extended_order_limit u z -> (forall n, `|u n| <= h%:E) ->
  (forall n, u n \is a fin_num) /\ z \is a fin_num.
Proof.
move=> hl hb; split.
- move=> n; rewrite fin_num_abs; exact: le_lt_trans (hb n) (ltry h).
- rewrite fin_num_abs; exact: le_lt_trans (extended_dominated_limit_bound hl hb) (ltry h).
Qed.

(** Source for [real_absolute_error_limit]: supporting pointwise
    convergence of |fn-g| to zero in Federer 2.4.9,
    p. 85, expressed for finite scalar values. *)
Lemma real_absolute_error_limit (R : realType) (u : nat -> R) (z : R) :
  extended_order_limit (fun n => (u n)%:E) z%:E ->
  extended_order_limit (fun n => `|u n-z|%:E) 0.
Proof.
move=> hl; apply: real_error_extended_order_limit=> e he.
have [N hN] := extended_finite_order_limit_error hl he; exists N=> n hn.
by rewrite subr0 normr_id; exact: hN.
Qed.

(** Source for [real_complement_error_limit]: the pointwise
    limit of 2h-|fn-g| in Federer 2.4.9, p. 85,
    with an arbitrary finite fixed complement c. *)
Lemma real_complement_error_limit (R : realType) (u : nat -> R) (z c : R) :
  extended_order_limit (fun n => (u n)%:E) z%:E ->
  extended_order_limit (fun n => (c-`|u n-z|)%:E) c%:E.
Proof.
move=> hl; apply: real_error_extended_order_limit=> e he.
have [N hN] := extended_finite_order_limit_error hl he; exists N=> n hn.
by rewrite addrAC subrr add0r normrN normr_id; exact: hN.
Qed.
