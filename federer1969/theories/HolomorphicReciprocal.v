(** Federer (1969), 3.4.12, p. 339: the actual
    reciprocal of a nonvanishing holomorphic function is holomorphic.
    Reuse its proved real analyticity and differentiate the original
    product identity to prove complex linearity of its differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexCoefficientAlgebra
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormDifferentialLinear NormDifferentialLocal
  NormDifferentialDirectional NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra
  NormAnalyticLocal NormRegularity NormAnalyticComplexReciprocal HolomorphicUP HolomorphicRestriction
  HolomorphicDifferentialUP HolomorphicDifferentialExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Reciprocals.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Variable A:X->Prop.
Variable f:X->C.
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation B:=(fun x=>A x /\f x!=0).

(** Source for [holomorphic_reciprocal]: the original local
    reciprocal used in the complex unit theorem extending
    3.4.7, p. 325, under 3.4.12, p. 339. The
    actual nonzero domain, including its openness, is retained. *)
Theorem holomorphic_reciprocal:
  is_holomorphic hNX hN A f ->is_holomorphic hNX hN B (fun x=>(f x)^-1).
Proof.
move=>hF.
have hInverse:=norm_analytic_complex_reciprocal hF.1.
have hOpen x (hx:B x):norm_domain_interior NX B x:=
  ((norm_analytic_class_all_orders hInverse 0%N).1 x hx).1.
have hRestricted:=@holomorphic_open_restriction R X C^o NX N hNX hN A B f
  (fun x hx=>hx.1) hOpen hF.
split;first exact:hInverse.
move=>a L ha hL.
have [D [LD [hLD hD]]]:=holomorphic_differential_exists hRestricted ha.
have hBound (z w:CR):N (complex_real_multiply z w)<=1*(N z*N w).
  by rewrite mul1r /complex_real_multiply complex_modulus_mul.
have hProduct:=@norm_differential_bilinear_product R XR CR CR CR NX N N N
  hNX hN hN hN (@complex_real_multiply R) (@complex_real_multiply_bilinear R)
  1 B f (fun x=>(f x)^-1) a LD L ler01 hBound hLD hL.
have hConstant:=@norm_differential_domain_agreement R XR CR NX N hNX B
  (fun x=>complex_real_multiply (f x) (f x)^-1) (fun _=>1) a
  (norm_bilinear_product_linear_term (@complex_real_multiply_bilinear R) (f a) (f a)^-1 LD L)
  (fun x hx=>mulfV hx.2) hProduct.
have hZero:=norm_differential_unique hNX hN hConstant
  (@norm_differential_constant R XR CR NX N hNX hN B a 1 (hOpen a ha)).
have hEquation x:LD x*(f a)^-1+f a*L x=0.
  have h:=congr1 (fun M:Hom XR CR=>M x) hZero.
  exact:h.
have hInverseEquation x:f a*L x= -(LD x*(f a)^-1).
  apply/eqP;by rewrite -addr_eq0 addrC hEquation eqxx.
have hComplex:=hRestricted.2 a LD ha hLD.
move=>c x.
change (L (c*:(x:X))=c*(L x)).
apply:(mulfI ha.2).
rewrite hInverseEquation [f a*(c*L x)]mulrCA hInverseEquation hComplex.
change (-((c*LD x)*(f a)^-1)=c*(-(LD x*(f a)^-1))).
ring.
Qed.
End Reciprocals.
