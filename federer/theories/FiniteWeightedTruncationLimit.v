(** Federer (1969), 3.2.20, p. 257: supporting increasing
    limits of finite weighted truncations, applying 2.4.7, p. 84,
    to the extended-real weight in the area transformation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit ExtendedTruncationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_increasing_finite_right_scale]: supporting
    scalar limit for the truncation argument in Federer 3.2.20,
    p. 257. A nonnegative finite multiplier preserves increasing
    convergence, including zero times either infinity. *)
Lemma extended_increasing_finite_right_scale (R : realType)
    (u : nat -> \bar R) (z : \bar R) (b : R) :
  (0<=b)%R -> extended_increases_to u z ->
  extended_increases_to (fun n=>u n* b%:E) (z* b%:E).
Proof.
move=> hb hu; case: (eqVneq b 0%R)=> [->|hbNe].
- split.
  + by move=> i j hij; rewrite !mule0.
  + split; move=> a ha; exists 0%N=> n hn; by rewrite !mule0 in ha *.
have hbPos : (0<b)%R by rewrite lt_neqAle eq_sym hbNe hb.
have hbE : 0<=b%:E by rewrite lee_fin.
split.
- move=> i j hij; exact: (lee_wpmul2r hbE (hu.1 i j hij)).
- split.
  + move=> a ha.
    have ha' : a* (b^-1)%R%:E<z by rewrite lte_pdivrMr.
    have [N hN] := hu.2.1 _ ha'.
    exists N=> n hn; rewrite -(@lte_pdivrMr R b (u n) a hbPos); exact: (hN n hn).
  + move=> a ha.
    have ha' : z<a* (b^-1)%R%:E by rewrite lte_pdivlMr.
    have [N hN] := hu.2.2 _ ha'.
    exists N=> n hn; rewrite -(@lte_pdivlMr R b (u n) a hbPos); exact: (hN n hn).
Qed.

(** Source for [finite_weighted_truncations_increase]: supporting
    pointwise convergence of the clipped weighted integrands in
    Federer 3.2.20, p. 257. No finiteness of the original
    extended-real weight is needed. *)
Lemma finite_weighted_truncations_increase (R : realType) (z : \bar R) (b : R) :
  (0<=b)%R -> extended_increases_to
    (fun n=>(Order.min z (n.+1)%:R%:E)* b%:E) (z* b%:E).
Proof.
move=> hb; exact: (extended_increasing_finite_right_scale hb
  (extended_natural_upper_truncations_increase z)).
Qed.
