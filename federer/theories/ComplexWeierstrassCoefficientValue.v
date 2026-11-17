(** Federer (1969), 3.4.12, p. 339: original complex
    mixed coefficients equal the actual derivative on the two
    repeated blocks, with the original factorial normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ContinuousMultilinearUP ContinuousMultilinearSealed MultilinearArguments
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassCoefficientUP WeierstrassFieldMixedFormValue WeierstrassMixedArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_split_coefficient_value]: the
    original evaluation on i copies of v and j copies
    of the included transverse vector, extending 3.4.6,
    p. 322, as required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_split_coefficient_value (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) i j (Cij:K->ComplexScalars.C R):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j Cij ->
  forall z,Cij z=(((i`!)%:R*(j`!)%:R)^-1:ComplexScalars.C R)*
    @ContinuousMultilinear.evaluation R (i+j)%N
      (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)
      (multilinear_arguments_join [ffun _:'I_i=>v] [ffun _:'I_j=>inclusion z])
      (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 (i+j)%N alpha).
Proof.
move=>hC z.
pose F:=@HolomorphicGermForms.value R X NX hNX 0 (i+j)%N alpha.
have hF:=@HolomorphicGermForms.laws R X NX hNX 0 (i+j)%N alpha.
have hArguments:=@weierstrass_joined_arguments_tuple X i j [ffun _:'I_i=>v] [ffun _:'I_j=>inclusion z].
have hLeft:[tuple [ffun _:'I_i=>v] r |r<i]=[tuple v |r<i].
  by apply:eq_from_tnth=>r;rewrite !tnth_mktuple ffunE.
have hRight:[tuple [ffun _:'I_j=>inclusion z] r |r<j]=[tuple inclusion z |r<j].
  by apply:eq_from_tnth=>r;rewrite !tnth_mktuple ffunE.
rewrite hLeft hRight in hArguments.
by rewrite (hC F hF z) weierstrass_field_mixed_form_value hF -hArguments.
Qed.
