(** Exact spherical values for the project counterexample to
    Federer 2.10.11, p. 176. Combine the existing source cover,
    target probability lower bound and corrected general image bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import BinaryPrefixMetric BinaryPrefixSphericalUpper BinaryVerticalEmbedding
  BinaryVerticalSphericalLower RealSphericalMultiplicityBound RealHausdorffMeasureLaws
  HausdorffMeasure MetricProductBackground RealMetricBackground RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_vertical_spherical_values]: the actual
    source and image have spherical lengths one and two, respectively.
    This project counterexample to the spherical parenthesis of
    Federer 2.10.11, p. 176, also proves the factor two is sharp
    in dimension one for a bound between arbitrary metric spaces. *)
Theorem binary_vertical_spherical_values (R:realType):
  @spherical_measure R (binary_prefix_metric R) 1 setT= 1 /\
  @spherical_measure R
    (metric_product (binary_prefix_metric R) (real_line_metric R)) 1
    ((@binary_vertical_embedding R) @` setT)= 2%:E.
Proof.
pose X:=binary_prefix_metric R.
pose Y:=metric_product X (real_line_metric R).
pose f:=@binary_vertical_embedding R.
have hbound:=@real_spherical_lipschitz_image_bound_corrected R X Y f 1%R 1%R
  (ler01:(0<=(1:R))%R) (@binary_vertical_embedding_lipschitz R) setT.
have hOne:real_power (2:R) 1= 2%R by apply:real_power_one_exponent;exact:ler0n.
rewrite hOne real_power_one_base mulr1
  -[1%R]/(1%:R:R) !real_spherical_measure_natural in hbound.
have hSource:=@binary_prefix_spherical_length_upper R.
have hTarget:=@binary_vertical_spherical_mass_lower R.
have hTwo:0<=(2:R)%:E by rewrite lee_fin ler0n.
have hUpper:=le_trans hbound (lee_wpmul2l hTwo hSource).
rewrite mule1 in hUpper.
have hValue:@spherical_measure R Y 1 (f @` setT)= 2%:E.
  apply/eqP;by rewrite eq_le hUpper hTarget.
rewrite hValue in hbound.
have hTwoPos:0<(2:R)%:E by rewrite lte_fin ltr0n.
have hTwoFinite:((2:R)%:E \is a fin_num) by rewrite fin_numE.
have hLower:1<=@spherical_measure R X 1 setT.
  rewrite -(lee_pmul2l hTwoFinite hTwoPos) mule1;exact hbound.
split;last exact hValue.
apply/eqP;by rewrite eq_le hSource hLower.
Qed.
