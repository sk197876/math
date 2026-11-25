(** Federer (1969), 4.1.5, p. 349: the original
    variation gauge exists, possibly infinite. A positive
    majorant admits the zero test, so the previously proved
    nonempty extended-real supremum theorem applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP FunctionLatticeUP ExtendedSupremumConstruction
  DistributionVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionVariationExistence.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.

(** Source for [distribution_variation_values_nonempty]: zero
    is an admissible test for every nonnegative majorant,
    so the supremum in Federer 4.1.5, p. 349, is nonempty. *)
Lemma distribution_variation_values_nonempty f:function_nonnegative f ->
  distribution_variation_values NY value S f !=set0.
Proof.
move=>hNonnegative; exists 0; exists (0:E); split.
- move=>x.
  have hValue:value (0:E) x=0:=congr1 (fun F:X->Y=>F x) (linear0 value).
  by rewrite hValue (real_seminorm_zero hNY.1).
- exact:linear0.
Qed.

(** Source for [distribution_variation_value_exists]: existence
    of the original ||S||(f), possibly infinite, in Federer
    4.1.5, p. 349. The supremum theorem supplies the witness
    after admissibility has been proved. *)
Theorem distribution_variation_value_exists f:function_nonnegative f ->
  exists c: \bar R,is_distribution_variation_value NY value S f c.
Proof.
move=>hNonnegative.
exact:(@extended_supremum_exists R (distribution_variation_values NY value S f)
  (@distribution_variation_values_nonempty f hNonnegative)).
Qed.
End DistributionVariationExistence.
