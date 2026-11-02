(** Federer (1969), 2.4.10, p. 85: supporting nonnegativity and subset
    monotonicity for the zero extensions of a nonnegative density.
    Measurability of the density or the subsets is not assumed here. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_extension_nonnegative_almost]: the zero
    extension of the nonnegative density remains nonnegative
    almost everywhere, supporting Federer 2.4.10, p. 85. *)
Lemma zero_extension_nonnegative_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_function_zero_extension (0 : extended_real_line R) A f)).
Proof.
move=> hp; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp).
move=> x [y [hy hpos]]; have [ha|ha] := pselect (A x).
- exists y; split=> //; apply/partial_function_zero_extension_graph; left; by split.
- exists 0; split=> //; apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [nonnegative_zero_extension_subset_order]: supporting
    subset comparison of density restrictions in Federer
    2.4.10, p. 85, for arbitrary subsets A and B. *)
Lemma nonnegative_zero_extension_subset_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X)
    (f : partial_function X (extended_real_line R)) :
  A `<=` B -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_almost_everywhere mu (partial_extended_le_locus
    (partial_function_zero_extension (0 : extended_real_line R) A f)
    (partial_function_zero_extension (0 : extended_real_line R) B f)).
Proof.
move=> hAB hp; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp).
move=> x [y [hy hpos]]; have [ha|ha] := pselect (A x).
- exists y,y; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split=> //; apply/partial_function_zero_extension_graph; left; split=> //; exact: hAB.
- have hAz : partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) A f) x 0.
    apply/partial_function_zero_extension_graph; right; by split.
  have [hb|hb] := pselect (B x).
  + exists 0,y; split=> //; split=> //; apply/partial_function_zero_extension_graph; left; by split.
  + exists 0,0; split=> //; split=> //; apply/partial_function_zero_extension_graph; right; by split.
Qed.
