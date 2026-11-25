(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasurePushforward MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pushforward_almost_equal_precompose]: supporting null
    replacement in Federer 2.4.18(1), pp. 90–91 Equality requires both
    values to exist, so partial domains are preserved without treating two
    undefined values as equal. *)
Lemma pushforward_almost_equal_precompose (R : realType) (X Y : choiceType) (Z : Type)
    (mu : set X -> \bar R) (u : X -> Y) (f g : partial_function Y Z) :
  measure_almost_equal (measure_pushforward u mu) f g ->
  measure_almost_equal mu (partial_function_precompose u f) (partial_function_precompose u g).
Proof.
by rewrite /measure_almost_equal /measure_almost_everywhere /measure_pushforward preimage_setC.
Qed.

(** Source for [pushforward_nonnegative_almost_precompose]: supporting
    transfer of nonnegativity in the nonnegative case of Federer
    2.4.18(1), proof p. 91. More generally any
    predicate on values pulls back with its exact null exception. *)
Lemma pushforward_nonnegative_almost_precompose (R : realType) (X Y : choiceType) (Z : Type)
    (mu : set X -> \bar R) (u : X -> Y) (f : partial_function Y Z) (A : set Z) :
  measure_almost_everywhere (measure_pushforward u mu) (partial_function_preimage f A) <->
  measure_almost_everywhere mu (partial_function_preimage (partial_function_precompose u f) A).
Proof.
by rewrite /measure_almost_everywhere /measure_pushforward preimage_setC partial_function_precompose_preimage.
Qed.
