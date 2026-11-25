(** Federer (1969), 2.4.1, pp. 80–81: sums and scalar multiples preserve
    countable images. These elementary set-theoretic consequences support
    the step-function laws. Source context: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionPair
  PartialFunctionPostcomposition MeasurableRealArithmetic MeasureStepFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_postcomposition_range]: supporting image
    identity for the scalar operation in Federer 2.4.1, p. 80. *)
Lemma partial_postcomposition_range (X Y Z : Type) (u : partial_function X Y) (g : Y -> Z) :
  partial_function_range (partial_function_postcompose u g) = g @` partial_function_range u.
Proof.
apply/seteqP; split=> z.
- move=> [x [y [hy he]]]; exists y=> //; by exists x.
- move=> [y [x hx] he]; exists x; exists y; by split.
Qed.

(** Source for [partial_pair_range_subset]: the common-domain
    pair image is contained in the product of the two ranges,
    supporting countability in Federer 2.4.1, pp. 80–81. *)
Lemma partial_pair_range_subset (X Y Z : Type) (u : partial_function X Y) (v : partial_function X Z) :
  partial_function_range (partial_function_pair u v) `<=`
    partial_function_range u `*` partial_function_range v.
Proof. move=> [y z] [x [hy hz]]; split; by exists x. Qed.

(** Source for [partial_pair_range_countable]: supporting
    countability of common refinement values in Federer 2.4.1,
    pp. 80–81. *)
Lemma partial_pair_range_countable (X Y Z : Type) (u : partial_function X Y) (v : partial_function X Z) :
  countable (partial_function_range u) -> countable (partial_function_range v) ->
  countable (partial_function_range (partial_function_pair u v)).
Proof.
move=> hu hv.
have hi := @partial_pair_range_subset X Y Z u v.
exact: sub_countable (subset_card_le hi) (@countableX Y Z _ _ hu hv).
Qed.

(** Source for [partial_postcomposition_range_countable]: supporting
    countability under scalar multiplication in Federer 2.4.1,
    p. 80; any postcomposition preserves countable range. *)
Lemma partial_postcomposition_range_countable (X Y Z : Type) (u : partial_function X Y) (g : Y -> Z) :
  countable (partial_function_range u) -> countable (partial_function_range (partial_function_postcompose u g)).
Proof. move=> hu; rewrite partial_postcomposition_range; exact: sub_countable (card_image_le g _) hu. Qed.

(** Source for [partial_real_sum_range_countable]: direct
    countability of the image of u+v in Federer 2.4.1,
    p. 80, final paragraph. *)
Lemma partial_real_sum_range_countable (R : realType) (X : Type)
    (u v : partial_function X (real_line_metric R)) :
  countable (partial_function_range u) -> countable (partial_function_range v) ->
  countable (partial_function_range (partial_real_function_add u v)).
Proof.
move=> hu hv; apply: partial_postcomposition_range_countable.
exact: partial_pair_range_countable hu hv.
Qed.
