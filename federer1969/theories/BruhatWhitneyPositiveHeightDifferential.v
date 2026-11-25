(** Federer (1969), 3.4.10, p. 338:
    differentiate the original surface curves' actual
    height b(1+sqrt(1+4t))/2 at zero.
    Apply the already proved affine and square-root
    differentials and the ordinary chain rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology ring.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormDifferentialArithmetic NormDifferentialLocal NormDifferentialChain
  NormAffineDilationDifferentials NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra
  ScalarSquareRootDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_positive_height_differential]: the
    actual positive-axis curve has height derivative b,
    supporting the nonregularity example cited by
    3.4.10, p. 338. The full
    open discriminant domain is retained. *)
Theorem bruhat_whitney_positive_height_differential (R:realType) (b:R):
  has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    [set t|0<1+4*t] (fun t=>b*(1+Num.sqrt (1+4*t))/2) 0
    (@scalar_coefficient_linear_map R R^o b).
Proof.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose A:set R^o:=[set t|0<1+4*t].
have hAffine:has_norm_differential N N setT (fun t:R^o=>1+4*t) 0
    (@scalar_coefficient_linear_map R R^o 4).
  have hOriginal:=@norm_affine_dilation_differential R R^o N hN 4 1 0.
  have hMap:4*:hom_of_linear (linear_id R^o)=@scalar_coefficient_linear_map R R^o 4.
    apply:hom_ext=>t;change (4*t=t*4);exact:mulrC.
  rewrite hMap in hOriginal.
  apply:(norm_differential_domain_agreement hN _ hOriginal)=>t _.
  change (4*t+1= 1+4*t);exact:addrC.
have hSqrt:has_norm_differential N N (fun t:R^o=>0<t) Num.sqrt
    (1+4*0) (@scalar_coefficient_linear_map R R^o 2^-1).
  rewrite mulr0 addr0.
  have h:=@scalar_square_root_differential R 1 ltr01.
  by rewrite sqrtr1 mulr1 in h.
have hComposite:=@norm_differential_chain R R^o R^o R^o N N N hN hN hN
  setT (fun t=>0<t) (fun t=>1+4*t) Num.sqrt 0
  (@scalar_coefficient_linear_map R R^o 4)
  (@scalar_coefficient_linear_map R R^o 2^-1) hAffine hSqrt.
have hDomain:(fun t:R^o=>setT t /\0<1+4*t)=A.
  apply:funext=>t;apply:propext;split;[by case|by move=>h;split].
change (has_norm_differential N N (fun t:R^o=>setT t /\0<1+4*t)
  (fun t=>Num.sqrt (1+4*t)) 0
  (hom_comp (@scalar_coefficient_linear_map R R^o 2^-1)
    (@scalar_coefficient_linear_map R R^o 4))) in hComposite.
rewrite hDomain in hComposite.
have hCoefficient:hom_comp (@scalar_coefficient_linear_map R R^o 2^-1)
    (@scalar_coefficient_linear_map R R^o 4)=@scalar_coefficient_linear_map R R^o 2.
  apply:hom_ext=>t;change ((t*4)*2^-1=t*2).
  field;rewrite ?pnatr_eq0 //.
rewrite hCoefficient in hComposite.
have hConstant:=@norm_differential_constant R R^o R^o N N hN hN A 0 1
  (norm_differential_interior hComposite).
have hSum:=norm_differential_add hN hConstant hComposite.
rewrite add0r in hSum.
have hScaled:=@norm_differential_scale R R^o R^o N N hN hN A
  (fun t=>1+Num.sqrt (1+4*t)) 0 (@scalar_coefficient_linear_map R R^o 2) (b/2) hSum.
have hMap:(b/2)*:(@scalar_coefficient_linear_map R R^o 2)=
    @scalar_coefficient_linear_map R R^o b.
  apply:hom_ext=>t;change ((b/2)*(t*2)=t*b).
  field;rewrite ?pnatr_eq0 //.
rewrite hMap in hScaled.
apply:(norm_differential_domain_agreement hN _ hScaled)=>t _.
change ((b/2)*(1+Num.sqrt (1+4*t))=b*(1+Num.sqrt (1+4*t))/2);ring.
Qed.
