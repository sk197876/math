(** Elementary finite-product estimates supporting Federer (1969),
    3.1.1(4), p. 210. They separate one or two small factors from
    the remaining bounded factors in a multilinear remainder. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_product_bounded_factors]: a product over
    a subset of m factors, each between zero and B with B at least
    one, is at most B to the power m. This auxiliary estimate
    supports the remainder in 3.1.1(4), p. 210. *)
Lemma finite_product_bounded_factors (R : realType) m
    (a : 'I_m -> R) (P : pred 'I_m) (B : R) :
  1 <= B -> (forall i, P i -> 0 <= a i /\ a i <= B) ->
  (\prod_(i<m | P i) a i) <= B^+m.
Proof.
move=> hB ha.
have hb : (\prod_(i<m) if P i then a i else 1) <= \prod_(i<m) B.
  apply: ler_prod=> i _; apply/andP.
  case: ifP=> hi; first exact: ha i hi.
  exact: conj ler01 hB.
by rewrite -big_mkcond prodr_const card_ord in hb.
Qed.

(** Source for [finite_product_one_small_factor]: a single selected
    factor supplies a linear bound in the proof of 3.1.1(4), p. 210.
    The other factors are uniformly bounded by B. *)
Lemma finite_product_one_small_factor (R : realType) m
    (a : 'I_m -> R) (i : 'I_m) (B H : R) :
  1 <= B -> 0 <= H -> (forall k, 0 <= a k) -> a i <= H ->
  (forall k, k != i -> a k <= B) ->
  (\prod_(k<m) a k) <= H*(B^+m).
Proof.
move=> hB hH ha hi hb.
have ho : (\prod_(k<m | k != i) a k) <= B^+m.
  apply: finite_product_bounded_factors hB _=> k hk; exact: conj (ha k) (hb k hk).
rewrite (bigD1 i) //=.
apply: ler_pM.
- exact: ha.
- by apply: prodr_ge0=> k _; exact: ha.
- exact hi.
- exact ho.
Qed.

(** Source for [finite_product_two_small_factors]: two distinct
    selected factors supply the quadratic bound for the remainder
    in Federer 3.1.1(4), p. 210. *)
Lemma finite_product_two_small_factors (R : realType) m
    (a : 'I_m -> R) (i j : 'I_m) (B H K : R) :
  i != j -> 1 <= B -> 0 <= H -> 0 <= K ->
  (forall k, 0 <= a k) -> a i <= H -> a j <= K ->
  (forall k, k != i -> k != j -> a k <= B) ->
  (\prod_(k<m) a k) <= H*K*(B^+m).
Proof.
move=> hij hB hH hK ha hi hj hb.
have hji : j != i by rewrite eq_sym.
have ho : (\prod_(k<m | (k != i) && (k != j)) a k) <= B^+m.
  apply: finite_product_bounded_factors hB _=> k /andP [hki hkj].
  exact: conj (ha k) (hb k hki hkj).
rewrite (bigD1 i) //= (bigD1 j hji) /= -mulrA.
apply: ler_pM.
- exact: ha.
- apply: mulr_ge0; first exact: ha.
  by apply: prodr_ge0=> k _; exact: ha.
- exact hi.
- apply: ler_pM.
  + exact: ha.
  + by apply: prodr_ge0=> k _; exact: ha.
  + exact hj.
  + exact ho.
Qed.
