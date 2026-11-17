(** Federer (1969), 3.4.10, p. 338:
    verify the actual implicit equation for
    the cited surface near its negative axis.
    Reuse the scalar product, power, sum and
    difference rules already proved in Chapter 3. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormOpenDomainLaws NormHigherCurveDerivativeUP NormDifferentialLinear
  NormDifferentialArithmetic NormDifferentialSubtraction NormDifferentialScalarProduct
  ScalarPowerDifferentialComposition EuclideanScalarCoordinateMaps
  BruhatWhitneyAuxiliaryEquation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_auxiliary_differential]: the
    auxiliary equation has a nonzero derivative
    in its last coordinate when x=0 and z!=0.
    This supplies the actual inverse-theorem premise
    for the example cited in 3.4.10,
    p. 338; no implicit solution is assumed. *)
Theorem bruhat_whitney_auxiliary_differential (R:realType) (a:R_n R 3):
  let X:=R_n R 3 in
  let j:=Ordinal (isT:(1<3)%N) in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  a ord0=0 ->exists D:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) setT
      (@bruhat_whitney_auxiliary_equation R) a D /\
    forall u:X,u j=0 ->D u=a j*u ord_max.
Proof.
move=>X j NX hNX hA.
pose hN:=@scalar_absolute_value_norm R.
pose Dx:=@euclidean_scalar_coordinate_map R 3 ord0.
pose Dz:=@euclidean_scalar_coordinate_map R 3 j.
pose Dt:=@euclidean_scalar_coordinate_map R 3 ord_max.
have hDx:=@norm_differential_linear R X R^o NX (fun t:R^o=>`|t|)
  hNX hN setT a Dx (norm_full_domain_interior NX a) (euclidean_scalar_coordinate_bounded ord0).
have hDz:=@norm_differential_linear R X R^o NX (fun t:R^o=>`|t|)
  hNX hN setT a Dz (norm_full_domain_interior NX a) (euclidean_scalar_coordinate_bounded j).
have hDt:=@norm_differential_linear R X R^o NX (fun t:R^o=>`|t|)
  hNX hN setT a Dt (norm_full_domain_interior NX a) (euclidean_scalar_coordinate_bounded ord_max).
have hX2:=@norm_scalar_power_differential_composition R X NX hNX setT Dx a Dx 2 hDx.
change (has_norm_differential NX (fun t:R^o=>`|t|) setT (fun v:X=>(v ord0)^+2) a
  ((2%:R*(a ord0)^+1)*:Dx)) in hX2.
rewrite hA expr0n /= mulr0 scale0r in hX2.
have hZ2:=@norm_scalar_power_differential_composition R X NX hNX setT Dz a Dz 2 hDz.
have hT3:=@norm_scalar_power_differential_composition R X NX hNX setT Dt a Dt 3 hDt.
pose Z2:=(2%:R*(a j)^+1)*:Dz.
pose T3:=(3%:R*(a ord_max)^+2)*:Dt.
have hProduct1:=@norm_differential_scalar_product R X R^o NX (fun t:R^o=>`|t|)
  hNX hN setT (fun v:X=>(v j)^+2) (fun v:X=>(v ord0)^+2) a Z2 0 hZ2 hX2.
have hZero1:scalar_vector_product_linear_term ((a j)^+2) ((a ord0)^+2) Z2 0=0.
  apply:hom_ext=>u.
  change (Z2 u*(a ord0)^+2+(a j)^+2*0=0).
  rewrite hA;ring.
rewrite hZero1 in hProduct1.
have hProduct2:=@norm_differential_scalar_product R X R^o NX (fun t:R^o=>`|t|)
  hNX hN setT (fun v:X=>(v j)^+2*(v ord0)^+2) (fun v:X=>(v ord_max)^+3)
  a 0 T3 hProduct1 hT3.
have hZero2:scalar_vector_product_linear_term ((a j)^+2*(a ord0)^+2)
    ((a ord_max)^+3) 0 T3=0.
  apply:hom_ext=>u.
  change (0*(a ord_max)^+3+((a j)^+2*(a ord0)^+2)*T3 u=0).
  rewrite hA;ring.
rewrite hZero2 in hProduct2.
have hZT:=@norm_differential_scalar_product R X R^o NX (fun t:R^o=>`|t|)
  hNX hN setT Dz Dt a Dz Dt hDz hDt.
have hDifference:=norm_differential_subtract hNX hN hZT hProduct2.
have hConstant:=@norm_differential_constant R X R^o NX (fun t:R^o=>`|t|)
  hNX hN setT a 1 (norm_full_domain_interior NX a).
have hSum:=norm_differential_add hN hDifference hConstant.
rewrite subr0 addr0 in hSum.
exists (scalar_vector_product_linear_term (a j) (a ord_max) Dz Dt);split;first exact:hSum.
move=>u hu.
change (u j*a ord_max+a j*u ord_max=a j*u ord_max).
by rewrite hu mul0r add0r.
Qed.
