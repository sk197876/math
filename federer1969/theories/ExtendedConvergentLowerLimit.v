(** Federer (1969), 2.4.9, p. 85: the lower limit of a pointwise convergent
    sequence equals its limit, as used when applying Fatou to 2h-|fn-g|.
    These supporting scalar lemmas use only order-limit and supremum
    specifications. Source context: MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealOrderLimit ExtendedLowerLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_lower_limit_strict_eventual]: supporting
    eventual strict lower bound for the liminf in Federer
    2.4.9, p. 85; the supremum specification is sufficient. *)
Lemma extended_lower_limit_strict_eventual (R : realType) (u : nat -> \bar R) l b :
  is_extended_lower_limit u l -> b < l ->
  exists N, forall n, (N <= n)%N -> b < u n.
Proof.
move=> hl hb.
have [he|he] := pselect (exists c, extended_eventual_lower_bounds u c /\ b < c).
- have [c [[N hN] hbc]] := he; exists N=> n hn; exact: lt_le_trans hbc (hN n hn).
- exfalso; have hle : l <= b.
    apply: (extended_real_supremum_least hl)=> c hc.
    rewrite leNgt; apply/negP=> hbc; apply: he; exists c; by split.
  by move: hb; rewrite ltNge hle.
Qed.

(** Source for [extended_convergent_lower_limit]: supporting
    identification of the convergent pointwise lower limit in
    Federer 2.4.9, p. 85. Either infinite endpoint
    is allowed; the bounded-convergence proof uses finite limits. *)
Lemma extended_convergent_lower_limit (R : realType) (u : nat -> \bar R) l :
  extended_order_limit u l -> is_extended_lower_limit u l.
Proof.
move=> [hlo hup]; constructor.
- move=> b [N hN]; rewrite leNgt; apply/negP=> hlb.
  have [M hM] := hup b hlb.
  have hh := hM (maxn N M) (leq_maxr N M).
  by move: hh; rewrite ltNge (hN (maxn N M) (leq_maxl N M)).
- move=> b hb; rewrite leNgt; apply/negP=> hbl.
  have [q [hbq hql]] := @extended_rationals_order_dense R b l hbl.
  have [N hN] := hlo _ hql.
  have hqb : (ratr q : R)%:E <= b.
    apply: hb; exists N=> n hn; exact: ltW (hN n hn).
  by move: hbq; rewrite ltNge hqb.
Qed.
