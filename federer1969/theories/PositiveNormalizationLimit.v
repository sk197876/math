(** Elementary order-limit background supporting Federer (1969), 2.10.9, p.
    175: remove positive real normalizers which converge to a positive real
    limit. This is needed because beta_p I_p is monotone but the printed
    limit concerns I_p itself. Norm constants vary continuously by 2.4.17,
    p. 90. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit RealScalarOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [order_limits_eventually_strictly_ordered]:
    supporting elementary separation of two order limits
    for the normalizer removal in Federer 2.10.9, p. 175.
    This is background, not a separately printed book claim. *)
Lemma order_limits_eventually_strictly_ordered (R : realType)
    (u v : nat -> \bar R) (a b : \bar R) :
  extended_order_limit u a -> extended_order_limit v b -> a<b ->
  exists N, forall n, (N<=n)%N -> u n<v n.
Proof.
move=> hu hv hab; have [q [haq hqb]] := @extended_rationals_order_dense R a b hab.
have [K hK] := hu.2 (ratr q : R)%:E haq.
have [L hL] := hv.1 (ratr q : R)%:E hqb.
exists (maxn K L)=> n hn.
exact: lt_trans (hK n (leq_trans (leq_maxl K L) hn)) (hL n (leq_trans (leq_maxr K L) hn)).
Qed.

(** Source for [positive_normalization_sequence_limit]: supporting
    removal of beta factors from the measure limit in Federer
    2.10.9, p. 175. Only positivity and convergence of the
    real normalizers are needed; nonnegative measure values and
    their limit may be infinite. *)
Theorem positive_normalization_sequence_limit (R : realType) (c : nat -> R)
    (a : R) (u : nat -> \bar R) (z : \bar R) :
  (forall n, (0<c n)%R) -> (0<a)%R -> (forall n, 0<=u n) -> 0<=z ->
  extended_order_limit (fun n => (c n)%:E) a%:E ->
  extended_order_limit (fun n => (c n)%:E*u n) (a%:E*z) -> extended_order_limit u z.
Proof.
move=> hc ha hu hz hclim hvlim.
have hprod r : extended_order_limit (fun n => (c n)%:E*r%:E) (a%:E*r%:E).
  have hh := @real_scalar_order_limit R c a r hclim.
  have he : (fun n => (c n)%:E*r%:E)=(fun n => (r*c n)%R%:E).
    by apply: funext=> n; rewrite -EFinM mulrC.
  by rewrite he -EFinM mulrC.
split.
- move=> b hb.
  case: (ltP b 0)=> [hb0|hb0].
    exists 0%N=> n _; exact: lt_le_trans hb0 (hu n).
  have [q [hbq hqz]] := @extended_rationals_order_dense R b z hb.
  pose r := (ratr q : R).
  have hstrict : a%:E*r%:E<a%:E*z by rewrite lte_pmul2l // lte_fin.
  have [N hN] := @order_limits_eventually_strictly_ordered R
    (fun n => (c n)%:E*r%:E) (fun n => (c n)%:E*u n) _ _ (hprod r) hvlim hstrict.
  exists N=> n hn; apply: lt_trans hbq _.
  have hh := hN n hn; by move: hh; rewrite lte_pmul2l // lte_fin.
- move=> b hb.
  have [q [hzq hqb]] := @extended_rationals_order_dense R z b hb.
  pose r := (ratr q : R).
  have hstrict : a%:E*z<a%:E*r%:E by rewrite lte_pmul2l // lte_fin.
  have [N hN] := @order_limits_eventually_strictly_ordered R
    (fun n => (c n)%:E*u n) (fun n => (c n)%:E*r%:E) _ _ hvlim (hprod r) hstrict.
  exists N=> n hn; apply: lt_trans _ hqb.
  have hh := hN n hn; by move: hh; rewrite lte_pmul2l // lte_fin.
Qed.
