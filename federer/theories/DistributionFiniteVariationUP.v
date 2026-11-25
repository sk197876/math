(** Federer (1969), 4.1.5, p. 349: the original
    finiteness condition on K(U)+. Finite real
    supremum witnesses specify the condition independently
    of the opaque gauge implementation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  DistributionVariationUP DistributionVariationDomain DistributionVariationSealed DistributionVariationBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_finite_distribution_variation]: the
    literal condition ||S||(f)<infinity for every
    f in K(U)+, Federer 4.1.5, p. 349.
    The scalar functions live on the original U. *)
Definition is_finite_distribution_variation (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o):Prop:=
  forall f:set_type U->R,
    @positive_function_lattice R (set_type U)
      (@compactly_supported_continuous_functions R (set_type U)) f ->
    exists b:R,is_distribution_variation_value NY
      (@distribution_domain_values R X U Y E value) S f b%:E.

(** Source for [finite_distribution_variation_gauge_iff]:
    the independent finite-supremum specification is
    exactly the original strict infinite bound on the
    opaque gauge, Federer 4.1.5, p. 349. *)
Theorem finite_distribution_variation_gauge_iff (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o):
  is_finite_distribution_variation U NY value S <->
  forall (f:set_type U->R)
    (hf:@positive_function_lattice R (set_type U)
      (@compactly_supported_continuous_functions R (set_type U)) f),
    (@DistributionVariation.value R (set_type U) Y NY hNY E
      (@distribution_domain_values R X U Y E value) S f hf.2< +oo)%E.
Proof.
split.
- move=>hFinite f hf; have[b hB]:=hFinite f hf.
  have hGauge:=@DistributionVariation.laws R (set_type U) Y NY hNY E
    (@distribution_domain_values R X U Y E value) S f hf.2.
  have hEq:=distribution_variation_value_unique hGauge hB.
  rewrite hEq; exact:ltry.
- move=>hFinite f hf.
  have hGauge:=@DistributionVariation.laws R (set_type U) Y NY hNY E
    (@distribution_domain_values R X U Y E value) S f hf.2.
  have hNonnegative:=@distribution_variation_nonnegative R (set_type U) Y NY hNY E
    (@distribution_domain_values R X U Y E value) S f _ hf.2 hGauge.
  have hBound:=hFinite f hf.
  case:(@DistributionVariation.value R (set_type U) Y NY hNY E
    (@distribution_domain_values R X U Y E value) S f hf.2) hGauge hNonnegative hBound=>[b| |] hGauge hNonnegative hBound.
  + by exists b.
  + by rewrite ltxx in hBound.
  + by [].
Qed.
