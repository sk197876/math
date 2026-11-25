(** Federer (1969), 4.1.5, p. 349: opaque values of
    the original scalar-test variation gauge. The independent
    supremum specification and existence proof precede this
    choice. No Borel measure is introduced here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP FunctionLatticeUP DistributionVariationUP DistributionVariationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type DistributionVariationSignature.
(** Source for [value]: the original ||S||(f) supremum in
    Federer 4.1.5, p. 349, for a positive scalar majorant.
    Its restriction to K(U)+ is the printed gauge. *)
Parameter value:forall (R:realType) (X:choiceType) (Y:lmodType R)
  (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R)
  (ev:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o) (f:X->R),
  function_nonnegative f ->\bar R.
(** Source for [laws]: the actual gauge value has exactly the
    original least-upper-bound laws, Federer 4.1.5, p. 349. *)
Parameter laws:forall (R:realType) (X:choiceType) (Y:lmodType R)
  (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R)
  (ev:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o) (f:X->R)
  (hf:function_nonnegative f),
  is_distribution_variation_value NY ev S f (@value R X Y NY hNY E ev S f hf).
End DistributionVariationSignature.
Module DistributionVariation:DistributionVariationSignature.
(** Source for [value]: choose the already proved supremum
    witness behind an opaque interface, as required by the
    definition in Federer 4.1.5, p. 349. *)
Definition value (R:realType) (X:choiceType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R)
    (ev:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o) (f:X->R)
    (hf:function_nonnegative f): \bar R:=
  projT1 (cid (@distribution_variation_value_exists R X Y NY hNY E ev S f hf)).
(** Source for [laws]: the hidden supremum satisfies its
    independent original laws, Federer 4.1.5, p. 349. *)
Lemma laws (R:realType) (X:choiceType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R)
    (ev:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o) (f:X->R)
    (hf:function_nonnegative f):
  is_distribution_variation_value NY ev S f (@value R X Y NY hNY E ev S f hf).
Proof. exact:(projT2 (cid (@distribution_variation_value_exists R X Y NY hNY E ev S f hf))). Qed.
End DistributionVariation.
