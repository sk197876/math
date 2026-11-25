(** Supporting the last cost-limit equality in Federer (1969), 2.10.15, p.
    178: a positive finite beta factors through the supremum of partition
    costs. This is the numerical order law of 2.1.1, p. 51, not an
    additional geometric assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_finite_scaled_sequence_supremum]: supporting
    beta scaling in 2.10.15, p. 178, from the supremum
    definition in 2.1.1, p. 51. Infinite supremum values
    and negative individual terms are allowed. *)
Lemma positive_finite_scaled_sequence_supremum (R : realType)
    (u : nat -> \bar R) (a : \bar R) (c : R) : (0<c)%R ->
  is_extended_real_supremum [set z | exists n, z=u n] a ->
  is_extended_real_supremum [set z | exists n, z=c%:E*u n] (c%:E*a).
Proof.
move=> hc hs.
have hc0 : 0<=c%:E by rewrite lee_fin; exact: ltW hc.
have hi0 : 0<=((c^-1)%R)%:E by rewrite lee_fin invr_ge0; exact: ltW hc.
have hne : c!=0%R by rewrite gt_eqF.
constructor.
- move=> z [n ->].
  have hn : u n<=a.
    apply: (extended_real_supremum_upper hs); by exists n.
  exact (lee_wpmul2l hc0 hn).
- move=> b hb.
  have ha : a<=((c^-1)%R)%:E*b.
    apply: (extended_real_supremum_least hs)=> z [n ->].
    have hh := lee_wpmul2l hi0 (hb _ (ex_intro _ n (erefl _))).
    by rewrite muleA -EFinM mulVf // mul1e in hh.
  have hh := lee_wpmul2l hc0 ha.
  by rewrite muleA -EFinM mulfV // mul1e in hh.
Qed.
