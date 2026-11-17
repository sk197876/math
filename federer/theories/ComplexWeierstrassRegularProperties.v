(** Federer (1969), 3.4.12, p. 339: the original positive
    directional order excludes the zero direction and zero germ.
    Reuse actual bounded derivative evaluation and norm definiteness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermOperationsUP HolomorphicGermJetsSealed HolomorphicGermJetZeroNegate
  HolomorphicGermFormsUP HolomorphicGermFormsSealed ComplexWeierstrassRegularUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Regularity.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation jet:=(@HolomorphicGermJets.value R X NX hNXR 0).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i XR CR NX N hNXR hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i XR CR NX N hNXR hN).

(** Source for [complex_weierstrass_regular_germ_nonzero]: actual
    original directional regularity excludes the zero germ,
    extending 3.4.6, pp. 321–322, under 3.4.12, p. 339. *)
Lemma complex_weierstrass_regular_germ_nonzero (alpha:holomorphic_germ_space hNXR (0:X)) k v:
  is_complex_weierstrass_regular_germ hNX alpha k v ->alpha<>@holomorphic_germ_zero R X NX hNXR 0.
Proof.
move=>[_ [_ hTop]] hZero;apply:hTop.
by rewrite (@HolomorphicGermForms.laws R X NX hNX 0 k alpha) hZero holomorphic_germ_jet_zero linear0.
Qed.

(** Source for [complex_weierstrass_regular_direction_nonzero]: the
    original positive order forces v to be nonzero, extending
    3.4.6, p. 322, under 3.4.12, p. 339. No
    positive source-dimension hypothesis is added. *)
Lemma complex_weierstrass_regular_direction_nonzero (alpha:holomorphic_germ_space hNXR (0:X)) k v:
  is_complex_weierstrass_regular_germ hNX alpha k v ->v<>0.
Proof.
move=>[hK [_ hTop]] hv;subst v;apply:hTop.
rewrite (@HolomorphicGermForms.laws R X NX hNX 0 k alpha).
have hTuple:[ffun s=>tnth [tuple (0:X) | j<k] s]=[ffun _:'I_k=>(0:X)].
  by apply/ffunP=>s;rewrite !ffunE tnth_mktuple.
rewrite hTuple.
have hBound:=multilinear_operator_bound (continuous_multilinear_norm_laws (hZ k) (jet k alpha)) [ffun _:'I_k=>(0:X)].
have hProduct:(\prod_(i<k) NX ([ffun _:'I_k=>(0:X)] i))=0.
  under eq_bigr do rewrite ffunE (real_seminorm_zero hNXR.1).
  have hNonzero:k!=0%N by rewrite -lt0n.
  by rewrite prodr_const card_ord expr0n (negbTE hNonzero).
rewrite hProduct mulr0 in hBound.
apply:hN.2;apply/eqP;rewrite eq_le hBound /=;exact:complex_modulus_ge0.
Qed.
End Regularity.
