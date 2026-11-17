(** Federer (1969), 3.4.12, p. 339, extending the equation
    differentials in 3.4.8(10), p. 331. Apply the existing real
    chain and bilinear product rules to a complex prefix coefficient
    times a complex coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexCoefficientAlgebra ComplexModulus ComplexScalarNorm NormDifferentialUP
  NormDifferentialLinear NormDifferentialChain NormDifferentialLocal
  NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra
  NormRegularity NormClassOneUP NormAnalyticUP NormAnalyticLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_prefix_coordinate_differential]:
    in the original prefix kernel the differential of
    delta composed with p_m times omega_j equals
    delta(p_m(a)) omega_j. This is the complex version of the
    original triangular matrix calculation, 3.4.12, p. 339. *)
Theorem complex_prefix_coordinate_differential (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (U:Y->Prop) (P:Hom X Y)
    (xi:Hom X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o))
    (b:Y->ComplexScalars.C R) a:
  norm_domain_interior NX A a ->norm_bounded_linear NX NY P ->
  @norm_bounded_linear R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) xi ->
  (forall x,A x ->U (P x)) ->A a ->
  @norm_analytic R Y (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U b ->
  exists L:Hom X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o),
    @has_norm_differential R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) A (fun x=>b (P x)*xi x) a L /\
    forall v,P v=0 ->L v=b (P a)*xi v.
Proof.
move=>hInterior hP hXi hMaps ha hB.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose NC:=@complex_modulus R.
pose hNC:=@complex_modulus_real_norm R.
have [D hD]:=(norm_class_firstP hNY hNC U b).1
  (norm_analytic_class_all_orders hB 1%N).
have hDB:=norm_class_one_differential hD (hMaps a ha).
have hPLinear:=@norm_differential_linear R X Y NX NY hNX hNY A a P hInterior hP.
have hChain:=@norm_differential_chain R X Y CR NX NY NC hNX hNY hNC A U P b a
  P (D (P a)) hPLinear hDB.
have hCoefficient:=@norm_differential_restrict R X CR NX NC
  (fun x=>A x /\U (P x)) A (fun x=>b (P x)) a (hom_comp (D (P a)) P)
  (fun x hx=>conj hx (hMaps x hx)) hInterior hChain.
have hLinear:=@norm_differential_linear R X CR NX NC hNX hNC A a xi hInterior hXi.
pose L:=norm_bilinear_product_linear_term (@complex_real_multiply_bilinear R)
  (b (P a)) (xi a) (hom_comp (D (P a)) P) xi.
have hBound (z w:CR):NC (complex_real_multiply z w)<=1*(NC z*NC w).
  by rewrite /NC mul1r /complex_real_multiply complex_modulus_mul.
exists L;split.
- exact:(@norm_differential_bilinear_product R X CR CR CR NX NC NC NC
    hNX hNC hNC hNC (@complex_real_multiply R) (@complex_real_multiply_bilinear R)
    1 A (fun x=>b (P x)) xi a (hom_comp (D (P a)) P) xi
    ler01 hBound hCoefficient hLinear).
- move=>v hZero.
  change (D (P a) (P v)*xi a+b (P a)*xi v=b (P a)*xi v).
  by rewrite hZero linear0 mul0r add0r.
Qed.
