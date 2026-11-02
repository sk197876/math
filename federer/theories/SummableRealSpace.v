(** Federer (1969), 2.6.4, pp. 118–119: the vector spaces of total-domain
    summable real functions in the tensor diagram. Erratum p. 2, book p. 119
    lines 3, 4, 6, requires the total-domain notation. We keep literal
    functions, not classes modulo null functions. The subspace laws follow
    from 2.4.4(3)–(4), p. 82. his Chapter 18 does not state this tensor
    diagram. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP SummableRealFunctionUP TotalLoneSummability TotalScalarLpUP
  SummableRealSpaceUP SummableRealSpaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Space.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.
(** Source for [summable_real_space]: abstract total-domain L1
    space of Federer 2.6.4, pp. 118–119, following his
    erratum p. 2, book p. 119 lines 3, 4, 6. *)
Definition summable_real_space := @SummableRealSpace.space R X mu hm.
(** Source for [summable_real_value]: literal function evaluation
    for the corrected L1 space in Federer 2.6.4, p. 119. *)
Definition summable_real_value := @SummableRealSpace.value R X mu hm.
(** Source for [summable_real_value_injective]: supporting literal
    function identity for the monomorphism in Federer 2.6.4,
    p. 118. The proof uses only the abstract carrier laws. *)
Lemma summable_real_value_injective : injective summable_real_value.
Proof. exact: (SummableRealSpace.laws hm).1. Qed.
(** Source for [summable_real_value_summable]: membership in the
    total-domain L1 space of Federer 2.6.4, pp. 118–119. *)
Lemma summable_real_value_summable f : summable_real_functions mu (summable_real_value f).
Proof. apply: ((SummableRealSpace.laws hm).2 _).2; by exists f. Qed.
(** Source for [summable_real_value_lone]: compatibility with
    2.4.12, p. 86, for the corrected L1 diagram of
    Federer 2.6.4, p. 119. *)
Lemma summable_real_value_lone f : total_scalar_lp mu 1 (summable_real_value f).
Proof. exact (@summable_real_total_lone R X mu hm _ (summable_real_value_summable f)). Qed.
(** Source for [summable_real_value_surjective]: every total
    summable function occurs in the corrected L1 carrier in
    Federer 2.6.4, pp. 118–119. *)
Lemma summable_real_value_surjective f : summable_real_functions mu f ->
  exists v, summable_real_value v=f.
Proof. exact: ((SummableRealSpace.laws hm).2 f).1. Qed.
End Space.
Arguments summable_real_value {R X mu hm}.

(** Source for [summable_real_pack]: abstract carrier representative
    of a proved summable function for Federer 2.6.4, pp. 118–119.
    It is selected using only the exposed surjectivity law. *)
Definition summable_real_pack (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R)
    (hf : summable_real_functions mu f) : summable_real_space hm :=
  proj1_sig (cid (@summable_real_value_surjective R X mu hm f hf)).

(** Source for [summable_real_packE]: the exact function identity
    of the abstract representative used in Federer 2.6.4,
    pp. 118–119. It is stronger than almost-everywhere equality. *)
Lemma summable_real_packE (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R)
    (hf : summable_real_functions mu f) :
  summable_real_value (@summable_real_pack R X mu hm f hf)=f.
Proof. exact: proj2_sig (cid (@summable_real_value_surjective R X mu hm f hf)). Qed.
