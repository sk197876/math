(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),(8),
    pp. 328–329: original complex directional forms transform
    by the actual linear coordinate map. Use actual jet
    transport and the opaque complex-form evaluation laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  SymmetricForms ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermFormsUP
  HolomorphicGermFormsSealed HolomorphicGermJetsSealed PointedHolomorphicPullbackUP PointedHolomorphicLinearPullbackDiagonal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [pointed_holomorphic_linear_pullback_form_diagonal]:
    the exact original complex derivative diagonal, 3.4.12, p. 339. *)
Lemma pointed_holomorphic_linear_pullback_form_diagonal (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:is_complex_norm NX) (hNY:is_complex_norm NY) a b (L:Hom X Y)
    (P:holomorphic_germ_space (complex_norm_real hNY) b->holomorphic_germ_space (complex_norm_real hNX) a):
  is_pointed_holomorphic_germ_pullback L P ->L a=b ->
  forall k alpha v,@HolomorphicGermForms.value R X NX hNX a k (P alpha) [tuple v|_<k]=
    @HolomorphicGermForms.value R Y NY hNY b k alpha [tuple L v|_<k].
Proof.
move=>hP hCentre k alpha v.
rewrite !(@HolomorphicGermForms.laws R X NX hNX a k)
  !(@HolomorphicGermForms.laws R Y NY hNY b k).
have hTupleX:[ffun i=>tnth [tuple v|_<k] i]=[ffun _:'I_k=>v]
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
have hTupleY:[ffun i=>tnth [tuple L v|_<k] i]=[ffun _:'I_k=>L v]
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
rewrite hTupleX hTupleY.
exact:(@pointed_holomorphic_linear_pullback_diagonal R X Y NX NY
  (complex_norm_real hNX) (complex_norm_real hNY) a b L P hP hCentre k alpha v).
Qed.
