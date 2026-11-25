(** Federer (1969), 4.1.5, p. 349,
    used for the proper pushforward in
    4.1.7, p. 359: a finite bound
    for every admissible original test makes
    the literal original scalar-test supremum finite. *)
From mathcomp Require Import all_boot functions all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP FunctionLatticeUP DistributionVariationUP
  DistributionVariationExistence DistributionVariationBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [distribution_finite_gauge_from_test_bound]:
    the original finite-gauge condition follows
    from an actual finite test-action bound,
    supporting Federer 4.1.7, p. 359,
    by the independently specified supremum of
    4.1.5, p. 349. No finiteness
    conclusion is assumed. *)
Lemma distribution_finite_gauge_from_test_bound (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o) (f:X->R) (b:R):
  function_nonnegative f->
  (forall phi:E,(forall x,(NY (value phi x)<=f x)%R)->(S phi<=b)%R)->
  exists c:R,is_distribution_variation_value NY value S f c%:E /\(c<=b)%R.
Proof.
move=>hPositive hBound.
have [c hC]:=@distribution_variation_value_exists R X Y NY hNY E value S f hPositive.
have hNonnegative:=@distribution_variation_nonnegative R X Y NY hNY E value S f c hPositive hC.
have hUpper:=@distribution_variation_least_finite_bound R X Y NY E value S f c b hC hBound.
have hFinite:c < +oo:=le_lt_trans hUpper (ltry b).
case:c hC hNonnegative hUpper hFinite=>[c| |] hC hNonnegative hUpper hFinite.
- exists c;split;first exact:hC.
  by rewrite lee_fin in hUpper.
- by rewrite ltxx in hFinite.
- by [].
Qed.
