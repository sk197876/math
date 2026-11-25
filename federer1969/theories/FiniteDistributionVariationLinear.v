(** Federer (1969), 4.1.7, p. 358: the
    represented currents form a vector space.
    This supporting argument proves closure of
    the original finite compact-test gauge from
    4.1.5, p. 349. It requires no
    chosen representing measure or density. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  DistributionVariationDomain DistributionVariationUP DistributionVariationBasic
  DistributionVariationBoundedExistence DistributionFiniteVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FiniteDistributionVariationLinear.
Variable R:realType.
Variable X:topologicalType.
Variable U:set X.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Local Notation UT := [the choiceType of set_type U].
Local Notation values := (@distribution_domain_values R X U Y E value).
Local Notation finite := (@is_finite_distribution_variation R X U Y NY E value).

(** Source for [finite_distribution_variation_zero]:
    the zero functional has finite original
    compact-test gauges, supporting the normal-current
    vector spaces in Federer 4.1.7, p. 358. *)
Theorem finite_distribution_variation_zero:finite (0:Hom E R^o).
Proof.
move=>f hf.
apply:(@distribution_variation_bounded_value_exists R UT Y NY hNY E values
  (0:Hom E R^o) f 0 hf.2)=>phi _.
by rewrite hom_zeroE.
Qed.

(** Source for [finite_distribution_variation_linear]:
    every real linear combination retains finite
    original compact-test gauges, supporting the
    vector-space assertion of Federer 4.1.7,
    p. 358. Test bounds follow from
    the preceding absolute-gauge estimate. *)
Theorem finite_distribution_variation_linear c (S T:Hom E R^o):
  finite S->finite T->finite (c*:S+T).
Proof.
move=>hS hT f hf.
have[a hA]:=hS f hf.
have[b hB]:=hT f hf.
apply:(@distribution_variation_bounded_value_exists R UT Y NY hNY E values
  (c*:S+T) f (`|c|*a+b) hf.2)=>phi hPhi.
have hSBound:=@distribution_variation_absolute_bound R UT Y NY hNY E values S f a%:E hA phi hPhi.
have hTBound:=@distribution_variation_absolute_bound R UT Y NY hNY E values T f b%:E hB phi hPhi.
rewrite lee_fin in hSBound hTBound.
have hProduct:`|c|*`|S phi|<=`|c|*a:=
  ler_wpM2l (normr_ge0 c) hSBound.
have hAbsolute:`|c*S phi|<=`|c|*a by rewrite normrM.
have hScaled:c*S phi<=`|c|*a:=le_trans (ler_norm (c*S phi)) hAbsolute.
have hOther:T phi<=b:=le_trans (ler_norm _) hTBound.
rewrite hom_addE hom_scaleE.
exact:lerD hScaled hOther.
Qed.
End FiniteDistributionVariationLinear.
