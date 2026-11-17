(** Federer (1969), 3.4.12, p. 339:
    the original complex-valued holomorphic functions are
    closed under multiplication. Apply actual real analytic
    complex multiplication and the existing bilinear product rule. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed RealNormUP ComplexCoefficientAlgebra
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormDifferentialDirectional
  NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra NormAnalyticComplexProduct
  HolomorphicUP HolomorphicDifferentialUP HolomorphicDifferentialExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Product.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Variable A:X->Prop.
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation NC:=(@complex_modulus R).
Local Notation HOL f:=(@is_holomorphic R X C^o NX NC hNX hN A f).

(** Source for [holomorphic_product]: the multiplication
    closure required by the original holomorphic germ ring,
    3.4.12, p. 339. The actual complex
    product rule supplies its first differential. *)
Theorem holomorphic_product (f g:X->C):HOL f ->HOL g ->HOL (fun x=>f x*g x).
Proof.
move=>hF hG;split;first exact:norm_analytic_complex_product hF.1 hG.1.
move=>a L ha hActual.
have [D [LD [hLD hD]]]:=holomorphic_differential_exists hF ha.
have [E [LE [hLE hE]]]:=holomorphic_differential_exists hG ha.
have hBound (z w:CR):NC (complex_real_multiply z w)<=1*(NC z*NC w).
  by rewrite mul1r /complex_real_multiply complex_modulus_mul.
have hProduct:=@norm_differential_bilinear_product R XR CR CR CR NX NC NC NC
  hNX hN hN hN (@complex_real_multiply R) (@complex_real_multiply_bilinear R)
  1 A f g a LD LE ler01 hBound hLD hLE.
have hEqual:=norm_differential_unique hNX hN hActual hProduct.
have hLDc:=hF.2 a LD ha hLD.
have hLEc:=hG.2 a LE ha hLE.
move=>c x;rewrite hEqual.
change (LD (c*:(x:X))*g a+f a*LE (c*:(x:X))=
  c*(LD x*g a+f a*LE x)).
rewrite hLDc hLEc.
change ((c*LD x)*g a+f a*(c*LE x)=c*(LD x*g a+f a*LE x)).
ring.
Qed.
End Product.
