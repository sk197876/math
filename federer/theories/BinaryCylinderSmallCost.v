(** Decay of cylinder costs in the local counterexample to Federer (1969),
    2.3.8, p. 78. This reuses the self-contained geometric-power estimate
    developed for 2.2.6, p. 63. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import SequencePowerBounds BinaryCylinderCost BinaryWordEnumerationUP BinaryWordEnumerationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [binary_cylinder_cost_small]: sufficiently long
    prefixes have arbitrarily small covering costs, supporting
    convergence in measure in the local Federer 2.3.8 example. *)
Lemma binary_cylinder_cost_small (R : realType) (e : R) : (0 < e)%R ->
  exists k, forall w, (k <= size w)%N -> @binary_cylinder_cost R w < e%:E.
Proof.
move=> he; have [k hk] := sequence_inverse_power_small he; exists k=> w hw.
rewrite /binary_cylinder_cost lte_fin -exprVn.
apply: le_lt_trans _ hk; apply: ler_wiXn2l=> //.
- by rewrite invr_ge0 ler0n.
- by rewrite invf_le1 ?ltr0n // ler1n.
Qed.

(** Source for [binary_enumeration_cost_tends_zero]: costs along
    a bijective enumeration tend to zero, since only finitely
    many words have bounded length. Supporting the example for
    Federer 2.3.8, p. 78. *)
Lemma binary_enumeration_cost_tends_zero (R : realType) encode decode
    (he : is_binary_word_enumeration encode decode) (e : R) : (0 < e)%R ->
  exists K, forall n, (K <= n)%N -> @binary_cylinder_cost R (decode n) < e%:E.
Proof.
move=> hp; have [k hk] := binary_cylinder_cost_small hp.
have [K hK] := binary_enumeration_lengths_escape he k.
exists K=> n hn; apply: hk; exact: ltnW (hK n hn).
Qed.
