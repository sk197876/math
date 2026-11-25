(** Federer (1969), 4.1.5, pp. 349–350: elementary
    bounds of the original scalar-test variation gauge.
    Linearity of S and test evaluation supplies symmetry;
    the independent supremum laws retain infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP FunctionLatticeUP ExtendedSupremumUP
  DistributionVariationUP DistributionVariationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionVariationBasic.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.

(** Source for [distribution_variation_zero_admissible]: zero
    belongs to the original supremum set for each positive
    majorant in Federer 4.1.5, p. 349. *)
Lemma distribution_variation_zero_admissible f:function_nonnegative f ->
  distribution_variation_values NY value S f 0.
Proof.
move=>hNonnegative; exists (0:E); split.
- move=>x.
  have hValue:value (0:E) x=0:=congr1 (fun F:X->Y=>F x) (linear0 value).
  by rewrite hValue (real_seminorm_zero hNY.1).
- exact:linear0.
Qed.

(** Source for [distribution_variation_nonnegative]: the
    original ||S||(f) is nonnegative, including infinite
    values, Federer 4.1.5, p. 349. *)
Lemma distribution_variation_nonnegative f c:
  function_nonnegative f ->is_distribution_variation_value NY value S f c ->(0<=c)%E.
Proof.
move=>hf hC.
exact:(@extended_supremum_upper R _ c hC 0 (@distribution_variation_zero_admissible f hf)).
Qed.

(** Source for [distribution_variation_upper]: each original
    admissible test evaluation is bounded by ||S||(f),
    the displayed supremum in Federer 4.1.5, p. 349. *)
Lemma distribution_variation_upper f c:
  is_distribution_variation_value NY value S f c ->forall phi:E,
  (forall x,NY (value phi x)<=f x) ->((S phi)%:E<=c)%E.
Proof.
move=>hC phi hBound; apply:(@extended_supremum_upper R _ c hC (S phi)).
by exists phi.
Qed.

(** Source for [distribution_variation_absolute_bound]:
    |S(phi)| <= ||S||(f) for ||phi|| <= f, used for the
    original Cauchy estimate in Federer 4.1.5, p. 349.
    No finiteness or representation premise is imposed. *)
Theorem distribution_variation_absolute_bound f c:
  is_distribution_variation_value NY value S f c ->forall phi:E,
  (forall x,NY (value phi x)<=f x) ->((`|S phi|)%:E<=c)%E.
Proof.
move=>hC phi hBound.
have hPlus:=@distribution_variation_upper f c hC phi hBound.
have hNegative:forall x,NY (value (-phi) x)<=f x.
  move=>x.
  have hValue:value (-phi) x= -value phi x:=congr1 (fun F:X->Y=>F x) (linearN value phi).
  by rewrite hValue (real_seminorm_negate hNY.1).
have hMinus:=@distribution_variation_upper f c hC (-phi) hNegative.
rewrite linearN in hMinus.
case:(lerP 0 (S phi))=>hSign.
- by rewrite (ger0_norm hSign).
- by rewrite (ltr0_norm hSign).
Qed.

(** Source for [distribution_variation_monotone]: increasing
    the original scalar majorant increases the gauge, from
    the defining supremum of Federer 4.1.5, p. 349. *)
Theorem distribution_variation_monotone f g c d:
  is_distribution_variation_value NY value S f c ->
  is_distribution_variation_value NY value S g d ->
  (forall x,f x<=g x) ->(c<=d)%E.
Proof.
move=>hC hD hFG.
apply:(@extended_supremum_least R _ c hC d)=>r [phi [hBound hValue]].
rewrite -hValue; apply:(@distribution_variation_upper g d hD phi)=>x.
exact:(le_trans (hBound x) (hFG x)).
Qed.

(** Source for [distribution_variation_least_finite_bound]:
    any finite upper bound for the original admissible test
    evaluations bounds ||S||(f), the finite condition in
    Federer 4.1.5, p. 349. *)
Lemma distribution_variation_least_finite_bound f c b:
  is_distribution_variation_value NY value S f c ->
  (forall phi:E,(forall x,NY (value phi x)<=f x) ->S phi<=b) ->(c<=b%:E)%E.
Proof.
move=>hC hBound.
apply:(@extended_supremum_least R _ c hC b%:E)=>r [phi [hNorm hValue]].
rewrite -hValue lee_fin; exact:(@hBound phi hNorm).
Qed.
End DistributionVariationBasic.
