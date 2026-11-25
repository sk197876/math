(** Federer (1969), 4.1.5, p. 350: the
    original pointwise convolution bounds pass to T
    through its proved scalar limit. These supporting
    estimates retain the literal test gauge. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP CompactContinuousDomainFields CompactUniformApproximationUP
  DistributionVariationUP DistributionVariationBasic DistributionVariationFinite
  DistributionContinuousExtensionUP PositiveNormLimitUP PositiveRealLinearLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionExtensionApproximationBound.
Variable R:realType.
Variable X:topologicalType.
Variable U:set X.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.
Variable T:(X->Y)->R.
Hypothesis hT:is_distribution_continuous_extension U hNY value S T.

(** Source for [distribution_extension_approximation_upper]:
    the first original convolution bound gives
    T(h w)<=||S||(||w||), Federer 4.1.5,
    p. 350, by the proved positive-scale limit. *)
Theorem distribution_extension_approximation_upper (w:X->Y) (P:R->E) (f:X->R) b:
  compact_continuous_domain_fields U hNY w ->
  is_compact_uniform_test_approximation U NY value w P ->
  is_distribution_variation_value NY value S f b%:E ->
  (exists r:R,0<r /\ forall e:R,0<e ->e<r ->forall x,NY (value (P e) x)<=f x) ->
  T w<=b.
Proof.
move=>hw hApprox hGauge [r [hr hBound]].
have hLimit:=@distribution_extension_limit R X U Y NY hNY E value S T hT w hw P hApprox.
apply:(@positive_real_limit_eventual_upper R (fun e=>S (P e)) (T w) b hLimit).
exists r; split=>// e he her.
have h:=@distribution_variation_upper R X Y NY E value S f b%:E hGauge (P e) (hBound e he her).
by rewrite lee_fin in h.
Qed.

(** Source for [distribution_extension_approximation_scaled_bound]:
    the second original convolution bound gives
    |T(w-h w)|<=eta ||S||(g), supporting
    the last displayed estimate of Federer 4.1.5,
    p. 350. *)
Theorem distribution_extension_approximation_scaled_bound
    (w:X->Y) (P:R->E) (g:X->R) b eta:
  compact_continuous_domain_fields U hNY w ->
  is_compact_uniform_test_approximation U NY value w P ->
  is_distribution_variation_value NY value S g b%:E ->0<eta ->
  (exists r:R,0<r /\ forall e:R,0<e ->e<r ->
    forall x,NY (value (P e) x)<=eta*g x) ->
  `|T w|<=eta*b.
Proof.
move=>hw hApprox hGauge hEta [r [hr hBound]].
have hLimit:=@distribution_extension_limit R X U Y NY hNY E value S T hT w hw P hApprox.
apply:(@positive_real_limit_eventual_absolute_bound R (fun e=>S (P e)) (T w) (eta*b) hLimit).
exists r; split=>// e he her.
exact:(@distribution_variation_finite_scaled_bound R X Y NY hNY E value S g b eta
  hGauge hEta (P e) (hBound e he her)).
Qed.
End DistributionExtensionApproximationBound.
