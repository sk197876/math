(** Federer (1969), 2.1.1(6),(11), pp. 52-53: scalar multiplication and
    positive and negative parts. The zero factor uses the explicitly special
    product convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_part_scale]: Federer
    2.1.1(6), p. 52, supporting fact: nonnegative finite scalars
    factor out of the positive part. *)
Lemma extended_positive_part_scale (R : realType) (c : R) (x : \bar R) :
  (0 <= c)%R -> extended_positive_part (c%:E*x) = c%:E * extended_positive_part x.
Proof.
by move=> hc; rewrite /extended_positive_part maxe_pMr ?mule0 //; rewrite lee_fin.
Qed.

(** Source for [extended_negative_part_scale]: Federer
    2.1.1(6), p. 52, supporting corresponding negative-part identity. *)
Lemma extended_negative_part_scale (R : realType) (c : R) (x : \bar R) :
  (0 <= c)%R -> extended_negative_part (c%:E*x) = c%:E * extended_negative_part x.
Proof.
move=> hc; rewrite /extended_negative_part -muleN.
exact: extended_positive_part_scale.
Qed.

(** Source for [extended_positive_nonnegative_product]: Federer
    2.1.1(11), p. 53; a nonnegative second factor extracts the
    positive part of the real first factor, including zero and infinity. *)
Lemma extended_positive_nonnegative_product (R : realType) (c : R) (x : \bar R) :
  0 <= x -> extended_positive_part (c%:E*x) = (Num.max c 0)%:E*x.
Proof.
move=> hx; rewrite /extended_positive_part; have [hc|hc] := leP 0%R c.
- rewrite max_l; first by [].
  apply: mule_ge0 hx; by rewrite lee_fin.
- rewrite mul0e max_r //; apply: mule_le0_ge0 hx.
  by rewrite lee_fin; exact: ltW hc.
Qed.

(** Source for [extended_negative_nonnegative_product]: Federer 2.1.1(11),
    p. 53; the negative part of the real factor similarly factors out. *)
Lemma extended_negative_nonnegative_product (R : realType) (c : R) (x : \bar R) :
  0 <= x -> extended_negative_part (c%:E*x) = (Num.max (-c) 0)%:E*x.
Proof.
move=> hx; rewrite /extended_negative_part -mulNe -EFinN.
exact: extended_positive_nonnegative_product.
Qed.
