(** Federer (1969), 3.4.12, p. 339, extending the polynomial
    differentials in 3.4.8(10), p. 331. The existing real bilinear
    product rule applies to complex multiplication. This supplies the
    missing scalar-field connection; no complex calculus is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexCoefficientAlgebra ComplexModulus ComplexScalarNorm NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormDifferentialBilinearProduct
  NormBilinearDifferentialAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_scalar_power_differential]: the actual
    differential of an original complex coordinate power, supporting
    3.4.12, p. 339. The coefficient is the formal polynomial
    derivative, including exponent zero. Induction uses the proved
    bilinear product rule of 3.1.11, pp. 220–222. *)
Theorem complex_scalar_power_differential (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop)
    (f:X->ComplexScalars.C R) a
    (L:Hom X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)) n:
  @has_norm_differential R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) A f a L ->
  exists M:Hom X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o),
    @has_norm_differential R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) A (fun x=>f x^+n) a M /\
    forall v,M v=n%:R*f a^+n.-1*L v.
Proof.
move=>hF.
pose C:=ComplexScalars.C R.
pose CR:=restricted_space (ComplexScalars.embed R) C^o.
pose NC:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
have hBound (z w:CR):NC (complex_real_multiply z w)<=1*(NC z*NC w).
  by rewrite /NC mul1r /complex_real_multiply complex_modulus_mul.
elim:n=>[|n [M [hM hValue]]].
- exists (0:Hom X CR);split.
  + exact:(@norm_differential_constant R X CR NX NC hNX hN A a 1
      (norm_differential_interior hF)).
  + move=>v;by rewrite hom_zeroE mul0r mul0r.
- pose D:=norm_bilinear_product_linear_term (@complex_real_multiply_bilinear R)
    (f a^+n) (f a) M L.
  exists D;split.
  + have hProduct:=@norm_differential_bilinear_product R X CR CR CR NX NC NC NC
      hNX hN hN hN (@complex_real_multiply R) (@complex_real_multiply_bilinear R)
      1 A (fun x=>f x^+n) f a M L ler01 hBound hM hF.
    apply:(@norm_differential_domain_agreement R X CR NX NC hNX A _ _ a D _ hProduct)=>x _.
    by rewrite exprS mulrC.
  + move=>v.
    change (M v*f a+f a^+n*L v=n.+1%:R*f a^+n*L v).
    rewrite hValue.
    case:n hValue hM D=>[|n] hValue hM D.
    * rewrite !expr0;ring.
    * rewrite !exprSr -!natr1.
      ring.
Qed.
