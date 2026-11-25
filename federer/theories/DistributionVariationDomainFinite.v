(** Federer (1969), 4.1.5, p. 349: finite
    gauge on the original K(U)+ supplies every ambient
    compact majorant used by the convolution argument.
    Restriction and zero extension change no admissible
    test and add no finite-gauge hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric FunctionLatticeUP CompactSupportFunctionUP
  OpenSubspaceExtension CompactContinuousSubspaceSupport DistributionVariationUP DistributionVariationDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_domain_finite_majorants]:
    the original finiteness assumption in Federer
    4.1.5, p. 349, implies finiteness for every
    zero-normalized ambient compact majorant. *)
Theorem distribution_domain_finite_majorants (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (hOutside:forall phi:E,forall x:X,~U x ->value phi x=0)
    (S:Hom E R^o):
  (forall f:set_type U->R,
    @positive_function_lattice R (set_type U)
      (@compactly_supported_continuous_functions R (set_type U)) f ->
    exists b:R,is_distribution_variation_value NY
      (@distribution_domain_values R X U Y E value) S f b%:E) ->
  forall f:X->R,
    @positive_function_lattice R X (@compactly_supported_continuous_functions R X) f ->
    @real_function_support R X f `<=` U ->
    exists b:R,is_distribution_variation_value NY value S f b%:E.
Proof.
move=>hFinite f hf hSupport.
have hRestricted:=@compact_scalar_open_restriction R X U f hf.1 hSupport.
have hPositive:forall x:set_type U,0<=f (set_val x) by move=>x; exact:hf.2.
have[b hGauge]:=hFinite (fun x=>f (set_val x)) (conj hRestricted hPositive).
have hAmbient:=(@distribution_domain_gauge_value R X U Y NY hNY E value hOutside S
  (fun x=>f (set_val x)) b%:E).1 hGauge.
rewrite (@compact_scalar_open_restriction_inverse R X U f hSupport) in hAmbient.
by exists b.
Qed.
