(** Federer (1969), 3.4.8(10), p. 331:
    differentiate an original prefix coefficient
    times one suffix coordinate. Reuse the
    proved prefix chain rule, linear differential
    and scalar product rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialScalarProduct NormHigherCurveDerivativeUP NormRegularity NormClassOneUP
  NormAnalyticUP NormAnalyticLocal PrefixCoefficientDirectionalDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [prefix_coefficient_coordinate_differential]:
    on every direction in ker(p_m),
    D(delta composed with p_m times omega_j)
    equals delta(p_m(x)) omega_j, supporting
    the displayed determinant in 3.4.8(10), p. 331. *)
Theorem prefix_coefficient_coordinate_differential (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (U:Y->Prop) (P:Hom X Y) (xi:Hom X R^o) (b:Y->R) a:
  norm_domain_interior NX A a ->norm_bounded_linear NX NY P ->
  norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall x,A x ->U (P x)) ->A a ->
  @norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R) U b ->
  exists L:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) A (fun x=>b (P x)*xi x) a L /\
    forall v,P v = 0 ->L v = b (P a)*xi v.
Proof.
move=>hInterior hP hXi hMaps ha hB.
have [D hD]:=(norm_class_firstP hNY (@scalar_absolute_value_norm R) U b).1
  (norm_analytic_class_all_orders hB 1%N).
have hZero:P (0:X) = 0:=linear0 P.
have hDB:=norm_class_one_differential hD (hMaps a ha).
have hCoefficient:=(@prefix_coefficient_directional_differential R X Y NX NY hNX hNY
  A U P b a 0 (D (P a)) hInterior hP hMaps hZero hDB).1.
have hLinear:=@norm_differential_linear R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) A a xi hInterior hXi.
pose L:=scalar_vector_product_linear_term (b (P a)) (xi a) (hom_comp (D (P a)) P) xi.
exists L;split.
- exact:(@norm_differential_scalar_product R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) A (fun x=>b (P x)) xi a (hom_comp (D (P a)) P) xi hCoefficient hLinear).
- move=>v hV;rewrite /L /scalar_vector_product_linear_term hom_addE !hom_compE hom_scaleE hV linear0.
  change (0*xi a+b (P a)*xi v = b (P a)*xi v);by rewrite mul0r add0r.
Qed.
