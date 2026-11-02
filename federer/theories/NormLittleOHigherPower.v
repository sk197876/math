(** Federer (1969), 3.1.11, pp. 220–221:
    a remainder with one extra power is
    negligible at the requested Taylor order. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import NormLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_little_o_from_higher_power]:
    a local O(|t|^(k+1)) estimate implies
    the linewise o(|t|^k) assertion used
    to identify the coefficients of the
    inverse series in Federer 3.1.11,
    pp. 220–221. The coefficient may
    vanish, and k may be zero. *)
Theorem norm_little_o_from_higher_power (R : realType)
    (Y : lmodType R) (N : Y->R) (f : R->Y) k C r :
  0<=C -> 0<r ->
  (forall t, 0<`|t|<r -> N (f t)<=C*`|t|^+k.+1) ->
  norm_little_o_power N f k.
Proof.
move=>hC hr hb e he.
have hC1 : 0<C+1 by lra.
exists (Num.min r (e/(C+1))); split.
- by rewrite lt_min hr divr_gt0.
- move=>t /andP [ht0 ht].
  have /andP [htr hte] : (`|t|<r)&&(`|t|<e/(C+1)) by rewrite -lt_min.
  have hcsmall : C*`|t|<=e.
    have hh : (C+1)*`|t|<e.
      by move:hte; rewrite ltr_pdivlMr // mulrC.
    nra.
  apply: le_trans (hb t (introT andP (conj ht0 htr))) _.
  rewrite exprS mulrA.
  exact (ler_wpM2r (exprn_ge0 k (ltW ht0)) hcsmall).
Qed.
