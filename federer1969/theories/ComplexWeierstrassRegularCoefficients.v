(** Federer (1969), 3.4.12, p. 339: the original complex
    directional order supplies the lower zero rows and the
    nonzero divided leading coefficient used in the recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexScalarCharacteristicZero ComplexNormUP
  DividedPowers SymmetricForms HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassRegularUP ComplexWeierstrassCoefficientUP ComplexWeierstrassAxisCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Regularity.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Variable alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X).
Variable k:nat.
Variable v:X.
Variable inclusion:Hom K X.

(** Source for [complex_weierstrass_regular_low_coefficients]: the
    actual low distinguished rows vanish, extending 3.4.6,
    pp. 322–323, under 3.4.12, p. 339. *)
Lemma complex_weierstrass_regular_low_coefficients (Cij:nat->nat->K->ComplexScalars.C R):
  is_complex_weierstrass_regular_germ hNX alpha k v ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j (Cij i j)) ->
  forall i,(i<k)%N ->forall z,Cij i 0%N z=0.
Proof.
move=>[_ [hLow _]] hC i hi z.
by rewrite (complex_weierstrass_axis_coefficient_value (hC i 0%N) z) (hLow i hi) mulr0.
Qed.

(** Source for [complex_weierstrass_regular_leading_nonzero]: the
    original divided leading derivative is nonzero, permitting
    normalization without altering the original final hypotheses,
    3.4.12, p. 339, extending 3.4.6, p. 322. *)
Lemma complex_weierstrass_regular_leading_nonzero:
  is_complex_weierstrass_regular_germ hNX alpha k v ->
  ((((k`!)%:R)^-1:ComplexScalars.C R)*
    @HolomorphicGermForms.value R X NX hNX 0 k alpha [tuple v | j<k])<>0.
Proof.
move=>[_ [_ hNonzero]].
have hFact:=@characteristic_zero_factorial (ComplexScalars.C R) (@complex_scalar_characteristic_zero R) k.
apply/eqP;rewrite mulf_eq0 invr_eq0 (negbTE hFact) /=.
exact/eqP.
Qed.

(** Source for [complex_weierstrass_normalized_leading_coefficient]:
    after the temporary original scalar normalization the leading
    coefficient is one at every transverse point, extending
    3.4.6, pp. 322–323, under 3.4.12, p. 339. *)
Lemma complex_weierstrass_normalized_leading_coefficient (Cij:K->ComplexScalars.C R):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion k 0%N Cij ->
  ((((k`!)%:R)^-1:ComplexScalars.C R)*
    @HolomorphicGermForms.value R X NX hNX 0 k alpha [tuple v | j<k]) = 1 ->
  forall z,Cij z = 1.
Proof.
move=>hC hUnit z;by rewrite (complex_weierstrass_axis_coefficient_value hC z).
Qed.
End Regularity.
