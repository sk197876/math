(** Federer (1969), 3.4.12, p. 339, extending the displayed
    transverse derivatives in 3.4.8(10), p. 331. Reuse the existing
    bilinear product and finite-sum rules on the restricted real carrier
    of the original complex scalar field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexCoefficientAlgebra ComplexModulus ComplexScalarNorm NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormDifferentialFiniteCalculus
  NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra ComplexScalarPowerDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_polynomial_directional_differential]:
    the formal complex polynomial derivative is the actual
    differential in every direction annihilating the coefficient
    differentials. This is the complex counterpart of the original
    last-coordinate calculation, 3.4.12, p. 339. Empty families and
    zero powers remain. *)
Theorem complex_polynomial_directional_differential (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop) (a v:X) N
    (f:'I_N->X->ComplexScalars.C R)
    (D:'I_N->Hom X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o))
    (xi:Hom X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)):
  norm_domain_interior NX A a ->@norm_bounded_linear R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) xi ->
  (forall i,@has_norm_differential R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) A (f i) a (D i)) ->
  (forall i,D i v=0) ->
  exists L:Hom X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o),
    @has_norm_differential R X (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) A
      (fun x=>\sum_(i<N) f i x*(xi x)^+(i:nat)) a L /\
    L v=(\sum_(i<N) (i:nat)%:R*f i a*(xi a)^+(i:nat).-1)*xi v.
Proof.
move=>hInterior hXi hF hZero.
pose C:=ComplexScalars.C R.
pose CR:=restricted_space (ComplexScalars.embed R) C^o.
pose NC:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
have hXiD:=@norm_differential_linear R X CR NX NC hNX hN A a xi hInterior hXi.
have hPowerExists i:=@complex_scalar_power_differential R X NX hNX A xi a xi (i:nat) hXiD.
pose power i:=projT1 (cid (hPowerExists i)).
have hPower i:=projT2 (cid (hPowerExists i)).
pose term:=fun i:'I_N=>norm_bilinear_product_linear_term (@complex_real_multiply_bilinear R)
  (f i a) ((xi a)^+(i:nat)) (D i) (power i).
have hBound (z w:CR):NC (complex_real_multiply z w)<=1*(NC z*NC w).
  by rewrite /NC mul1r /complex_real_multiply complex_modulus_mul.
have hTerm i:@has_norm_differential R X CR NX NC A
    (fun x=>f i x*(xi x)^+(i:nat)) a (term i).
  exact:(@norm_differential_bilinear_product R X CR CR CR NX NC NC NC
    hNX hN hN hN (@complex_real_multiply R) (@complex_real_multiply_bilinear R)
    1 A (f i) (fun x=>(xi x)^+(i:nat)) a (D i) (power i)
    ler01 hBound (hF i) (hPower i).1).
pose L:=\sum_(i<N) term i.
exists L;split.
- have hSum:=@norm_differential_finite_sum R X CR NX NC hNX hN A a
    [the finType of 'I_N] predT (fun i x=>f i x*(xi x)^+(i:nat)) term
    hInterior (fun i _=>hTerm i).
  apply:(@norm_differential_domain_agreement R X CR NX NC hNX A _ _ a L _ hSum)=>x _.
  by elim/big_rec2:_=>[|i c g _ <-].
- have hEvaluation:L v=\sum_(i<N) term i v.
    rewrite /L;by elim/big_rec2:_=>[|i c g _ <-];rewrite ?hom_addE ?hom_zeroE.
  rewrite hEvaluation mulr_suml;apply:eq_bigr=>i _.
  change (D i v*(xi a)^+(i:nat)+f i a*(power i v)=
    (i:nat)%:R*f i a*(xi a)^+(i:nat).-1*xi v).
  rewrite hZero (hPower i).2;ring.
Qed.
