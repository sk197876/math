(** Federer (1969), 3.4.12, p. 339: the zeroth complex
    mixed coefficient is the actual original representative value.
    Reuse the axis coefficient equation and actual order-zero jet law. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP
  SymmetricForms ContinuousMultilinearZero HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassCoefficientUP ComplexWeierstrassAxisCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_zeroth_coefficient_value]: the original
    Q_(0,0)=Q(0) identity needed in preparation, extending 3.4.6(2),
    p. 322, under 3.4.12, p. 339. Every original
    representative gives the same value. *)
Lemma complex_weierstrass_zeroth_coefficient_value (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) (D:K->ComplexScalars.C R)
    (f:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion 0%N 0%N D ->
  holomorphic_germ f=alpha ->forall z,D z=holomorphic_representative_value f 0.
Proof.
move=>hD hRep z.
rewrite (complex_weierstrass_axis_coefficient_value hD z) /= invr1 mul1r
  (@HolomorphicGermForms.laws R X NX hNX 0 0%N alpha).
have hEmpty:[ffun s=>tnth [tuple v | j<0] s]=[ffun _:'I_0=>(0:X)]:=zero_arity_arguments_unique _ _.
rewrite hEmpty.
exact:(@HolomorphicGermJets.laws R X NX (complex_norm_real hNX) 0 0%N alpha f hRep).2.
Qed.
