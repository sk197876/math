(** Federer (1969), 2.3.2, p. 73, second paragraph: measurable total
    extensions and their almost equality with the original function. Proofs
    use only abstract graph preservation, with existence supplied by the
    sealed interface. Source context and the necessary empty-target
    qualification are documented in PartialFunctionExtensionUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed MeasureUP
  MeasureAlmostUP MeasurableFunctionUP MeasurableAlmostModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_extension_agreement]: supporting
    exact agreement locus for the extension remark in Federer
    2.3.2, p. 73. It is the original partial domain. *)
Lemma partial_function_extension_agreement (X Y : Type)
    (f : partial_function X Y) (h : X -> Y) :
  is_partial_function_total_extension f h ->
  partial_function_agreement f (partial_function_total h) = partial_function_domain f.
Proof.
move=> he; apply/seteqP; split=> x.
- by move=> [y [hy _]]; exists y.
- move=> [y hy]; exists y; split=> //; exact: he hy.
Qed.

(** Source for [partial_function_total_extension_almost_equal]:
    direct almost equality assertion in Federer 2.3.2, p. 73,
    for any extension of a function with conull domain. *)
Lemma partial_function_total_extension_almost_equal (R : realType) (X : choiceType)
    (Y : Type) (mu : set X -> \bar R) (f : partial_function X Y) (h : X -> Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  is_partial_function_total_extension f h ->
  measure_almost_equal mu f (partial_function_total h).
Proof.
move=> hd he; rewrite /measure_almost_equal (partial_function_extension_agreement he).
exact hd.
Qed.

(** Source for [measurable_function_total_extension]: precise
    version of Federer 2.3.2, p. 73, second paragraph, with
    a supplied target point. The extension has domain all of X,
    is almost equal to f and remains measurable. *)
Theorem measurable_function_total_extension (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) (y0 : Y) :
  is_measure_measurable_function mu f -> exists h : X -> Y,
    is_partial_function_total_extension f h /\
    measure_almost_equal mu f (partial_function_total h) /\
    is_measure_measurable_function mu (partial_function_total h).
Proof.
move=> hf; exists (@PartialFunctionExtension.value X Y f y0).
have he := @PartialFunctionExtension.laws X Y f y0.
have ha := @partial_function_total_extension_almost_equal R X Y mu f _
  (measurable_function_domain hf) he.
split=> //; split=> //; exact (@measurable_function_almost_equal R X Y mu hm f _ hf ha).
Qed.
