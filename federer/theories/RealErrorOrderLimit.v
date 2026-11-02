(** Federer (1969), 2.4.9, p. 85: supporting scalar conversion from errors
    tending to zero to convergence of integral values. Source context:
    MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_error_extended_order_limit]: supporting
    epsilon formulation of the finite limit in Federer 2.4.9,
    p. 85, using the project's order-interval limit convention. *)
Lemma real_error_extended_order_limit (R : realType) (u : nat -> R) (a : R) :
  (forall e : R, (0 < e)%R -> exists N, forall n, (N <= n)%N -> (`|u n-a| < e)%R) ->
  extended_order_limit (fun n => (u n)%:E) a%:E.
Proof.
move=> he; split.
- move=> b hb; have [q [hbq hqa]] := @extended_rationals_order_dense R b a%:E hb.
  have hpos : (0 < a-ratr q)%R by rewrite subr_gt0; exact hqa.
  have [N hN] := he _ hpos; exists N=> n hn.
  apply: lt_trans hbq _; rewrite lte_fin.
  have h := ltr_distlCBl (hN n hn).
  by rewrite opprB addrCA subrr addr0 in h.
- move=> b hb; have [q [haq hqb]] := @extended_rationals_order_dense R a%:E b hb.
  have hpos : (0 < ratr q-a)%R by rewrite subr_gt0; exact haq.
  have [N hN] := he _ hpos; exists N=> n hn.
  apply: lt_trans _ hqb; rewrite lte_fin.
  have h := ltr_distlDr (hN n hn).
  by rewrite addrCA subrr addr0 in h.
Qed.

(** Source for [extended_finite_order_limit_error]: supporting
    converse epsilon criterion for the pointwise limit used
    in Federer 2.4.9, p. 85. *)
Lemma extended_finite_order_limit_error (R : realType) (u : nat -> R) (a e : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E -> (0 < e)%R ->
  exists N, forall n, (N <= n)%N -> (`|u n-a| < e)%R.
Proof.
move=> [hlo hup] he.
have hlow : (a-e)%:E < a%:E by rewrite lte_fin ltrBlDr ltrDl.
have hupp : a%:E < (a+e)%:E by rewrite lte_fin ltrDl.
have [N hN] := hlo _ hlow; have [M hM] := hup _ hupp.
exists (maxn N M)=> n hn; rewrite ltr_distl; apply/andP; split.
- exact: hN n (leq_trans (leq_maxl N M) hn).
- exact: hM n (leq_trans (leq_maxr N M) hn).
Qed.

(** Source for [real_integral_error_comparison_limit]: supporting
    final implication of Federer 2.4.9, p. 85:
    an upper bound tending to zero for absolute integral
    differences forces convergence of the integral values. *)
Lemma real_integral_error_comparison_limit (R : realType) (u e : nat -> R) (a : R) :
  (forall n, (`|u n-a| <= e n)%R) ->
  extended_order_limit (fun n => (e n)%:E) 0 ->
  extended_order_limit (fun n => (u n)%:E) a%:E.
Proof.
move=> hbound hlim; apply: real_error_extended_order_limit=> r hr.
have [N hN] := hlim.2 r%:E hr; exists N=> n hn.
exact: le_lt_trans (hbound n) (hN n hn).
Qed.
