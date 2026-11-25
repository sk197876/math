(** Federer (1969), 2.4.17, p. 90: continuity of the positive reciprocal
    exponent. This supporting order-interval proof handles positive finite
    limiting exponents. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_reciprocal_order_limit]: scalar reciprocal
    continuity supporting the varying-root step of Federer 2.4.17, p. 90 *)
Lemma positive_reciprocal_order_limit (R : realType) (u : nat -> R) (l : R) :
  (forall n, (0 < u n)%R) -> (0 < l)%R ->
  extended_order_limit (fun n => (u n)%:E) l%:E ->
  extended_order_limit (fun n => ((u n)^-1)%:E) (l^-1)%:E.
Proof.
move=> hu hl [hlo hup]; have hli : (0 < l^-1)%R by rewrite invr_gt0.
split.
- move=> a ha; case: a ha=> [a| |] ha; last first.
  + exists 0%N=> n hn; exact: ltNyr.
  + by move: ha; rewrite ltNge leey.
  have [ha0|ha0] := leP a 0%R.
  + exists 0%N=> n hn; rewrite lte_fin.
    apply: le_lt_trans ha0 _; by rewrite invr_gt0.
  have hla : l%:E < (a^-1)%:E.
    rewrite lte_fin -[l]invrK (@ltf_pV2 R (l^-1)%R a hli ha0); exact ha.
  have [k hk] := hup _ hla; exists k=> n hn.
  have hai : (0 < a^-1)%R by rewrite invr_gt0.
  rewrite lte_fin -[a]invrK (@ltf_pV2 R (a^-1)%R (u n) hai (hu n)).
  exact: hk n hn.
- move=> b hb; case: b hb=> [b| |] hb; last first.
  + by move: hb; rewrite ltNge leNye.
  + exists 0%N=> n hn; exact: ltry.
  have hb0 : (0 < b)%R := lt_trans hli hb.
  have hbl : (b^-1)%:E < l%:E.
    rewrite lte_fin -[l]invrK (@ltf_pV2 R b (l^-1)%R hb0 hli); exact hb.
  have [k hk] := hlo _ hbl; exists k=> n hn.
  have hbi : (0 < b^-1)%R by rewrite invr_gt0.
  rewrite lte_fin -[b]invrK (@ltf_pV2 R (u n) (b^-1)%R (hu n) hbi).
  exact: hk n hn.
Qed.

(** Source for [positive_reciprocal_infinity_order_limit]: Supporting
    Federer 2.4.17, p. 90. *)
Lemma positive_reciprocal_infinity_order_limit (R : realType) (u : nat -> R) :
  (forall n, (0 < u n)%R) -> extended_order_limit (fun n => (u n)%:E) +oo ->
  extended_order_limit (fun n => ((u n)^-1)%:E) 0.
Proof.
move=> hu hl; split.
- move=> a ha; exists 0%N=> n hn; apply: lt_le_trans ha _.
  rewrite lee_fin invr_ge0; exact: ltW (hu n).
- move=> b hb; case: b hb=> [b| |] hb; last first.
  + by move: hb.
  + exists 0%N=> n hn; exact: ltry.
  have hbi : (0 < b^-1)%R by rewrite invr_gt0.
  have [k hk] := hl.1 (b^-1)%:E (ltry _); exists k=> n hn.
  rewrite lte_fin -[b]invrK (@ltf_pV2 R (u n) (b^-1)%R (hu n) hbi).
  exact: hk n hn.
Qed.
