(** Federer (1969), 4.1.5, p. 349:
    a finite bound on every admissible original
    test implies a finite original gauge value.
    The zero test and proved supremum laws
    exclude both infinite endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP FunctionLatticeUP DistributionVariationUP DistributionVariationExistence DistributionVariationBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [distribution_variation_bounded_value_exists]:
    finite admissible test bounds yield the original
    finite-gauge condition of Federer 4.1.5,
    p. 349, including empty domains and zero targets. *)
Theorem distribution_variation_bounded_value_exists (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o)
    (f:X->R) B:
  function_nonnegative f ->
  (forall phi:E,(forall x,NY (value phi x)<=f x) ->S phi<=B) ->
  exists b:R,is_distribution_variation_value NY value S f b%:E.
Proof.
move=>hf hBound.
have[c hGauge]:=@distribution_variation_value_exists R X Y NY hNY E value S f hf.
have hNonnegative:=@distribution_variation_nonnegative R X Y NY hNY E value S f c hf hGauge.
have hUpper:=@distribution_variation_least_finite_bound R X Y NY E value S f c B hGauge hBound.
case:c hGauge hNonnegative hUpper=>[b| |] hGauge hNonnegative hUpper.
- by exists b.
- by rewrite leye_eq in hUpper.
- by [].
Qed.
