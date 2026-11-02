(** Federer (1969), 2.4.10, p. 85: restricting an integrable function to a
    measurable set preserves integrability. The supporting comparison here
    bounds each restricted nonnegative part by the corresponding original
    part. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_extension_nonnegative_postcomposition_order]:
    supporting comparison of restricted positive/negative parts
    for Federer 2.4.10, p. 85. The general scalar
    map p is nonnegative and sends zero to zero. *)
Lemma zero_extension_nonnegative_postcomposition_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) (p : extended_real_line R -> extended_real_line R) :
  p 0=0 -> (forall y, 0 <= p y) -> measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_extended_le_locus
    (partial_function_postcompose (partial_function_zero_extension (0 : extended_real_line R) A f) p)
    (partial_function_postcompose f p)).
Proof.
move=> hp0 hp hd; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [y hy].
have hright : partial_function_graph (partial_function_postcompose f p) x (p y) by exists y; split.
have [hx|hx] := pselect (A x).
- exists (p y),(p y); split.
  + exists y; split=> //; apply/partial_function_zero_extension_graph; left; by split.
  + by split.
- exists 0,(p y); split.
  + exists 0; split=> //; apply/partial_function_zero_extension_graph; right; by split.
  + split=> //; exact: hp.
Qed.
