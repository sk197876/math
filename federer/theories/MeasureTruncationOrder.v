(** Federer (1969), 2.4.11, proof p. 86: nonnegative truncations increase,
    remain below the original function and have finite scalar ceiling.
    Source context: PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialUpperTruncation
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_truncation_nonnegative]: supporting
    nonnegativity of gn in Federer 2.4.11, proof p. 86. *)
Lemma measure_upper_truncation_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) c :
  0 <= c -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_upper_truncation f c)).
Proof.
move=> hc hp; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp)=> x [z [hz hz0]].
exists (Order.min z c); split; first by exists z; split.
by rewrite le_min hz0 hc.
Qed.

(** Source for [measure_upper_truncation_below]: supporting
    comparison gn<=|f| in Federer 2.4.11, proof p. 86. *)
Lemma measure_upper_truncation_below (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) c :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_extended_le_locus (partial_upper_truncation f c) f).
Proof.
move=> hd; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [z hz].
exists (Order.min z c),z; split; first by exists z; split.
split=> //; by rewrite ge_min lexx orTb.
Qed.

(** Source for [measure_upper_truncation_increasing]: supporting
    comparison of successive truncations in Federer 2.4.11,
    proof p. 86, for arbitrary ordered ceilings. *)
Lemma measure_upper_truncation_increasing (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) c d :
  c <= d -> measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_extended_le_locus (partial_upper_truncation f c) (partial_upper_truncation f d)).
Proof.
move=> hcd hd; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [z hz].
exists (Order.min z c),(Order.min z d); split; first by exists z; split.
split; first by exists z; split.
exact: le_min2 (lexx _) hcd.
Qed.
