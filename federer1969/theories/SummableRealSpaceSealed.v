(** Federer (1969), 2.6.4, pp. 118–119: the vector spaces of total-domain
    summable real functions in the tensor diagram. Erratum p. 2, book p. 119
    lines 3, 4, 6, requires the total-domain notation. We keep literal
    functions, not classes modulo null functions. The subspace laws follow
    from 2.4.4(3)–(4), p. 82. his Chapter 18 does not state this tensor
    diagram. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP SummableRealSpaceUP SummableRealSpaceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SummableRealSpaceSignature.
(** Source for [space]: total-domain L1 carrier, Federer 2.6.4,
    pp. 118–119, with erratum p. 2, book p. 119. *)
Parameter space : forall (R : realType) (X : choiceType) (mu : set X -> \bar R),
  is_measure mu -> lmodType R.
(** Source for [value]: literal function evaluation, Federer 2.6.4,
    p. 118, for the corrected total-domain carrier. *)
Parameter value : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (hm : is_measure mu), {linear @space R X mu hm -> (X -> R^o)}.
(** Source for [laws]: abstract L1 membership and injectivity,
    Federer 2.6.4, pp. 118–119, with erratum p. 2. *)
Parameter laws : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (hm : is_measure mu), is_summable_real_space mu (@value R X mu hm).
End SummableRealSpaceSignature.
Module SummableRealSpace : SummableRealSpaceSignature.
(** Source for [space]: sealed carrier witness for Federer
    2.6.4, pp. 118–119, with the erratum's total-domain convention. *)
Definition space (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (hm : is_measure mu) := summable_carrier_space hm.
(** Source for [value]: sealed evaluation witness for Federer
    2.6.4, p. 118. *)
Definition value (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (hm : is_measure mu) := @summable_carrier_value R X mu hm.
(** Source for [laws]: proved carrier laws for Federer 2.6.4,
    pp. 118–119; the construction remains hidden. *)
Lemma laws (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (hm : is_measure mu) : is_summable_real_space mu (@value R X mu hm).
Proof. exact: summable_carrier_laws. Qed.
End SummableRealSpace.
