(** Federer (1969), 3.4.12, p. 339, extending the
    Taylor argument of 3.4.8(5), p. 328: all original
    divided directional coefficients determine the actual holomorphic
    germ. Reuse complex polarization and actual jet injectivity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  ComplexScalarCharacteristicZero SymmetricForms HomogeneousPolynomialFunctions ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  HolomorphicGermTaylorInjective HolomorphicGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_directional_coefficients_injective]:
    equality of every original divided diagonal coefficient implies
    equality of the original germs, extending 3.4.5, p. 319,
    and 1.10.4, p. 46, under 3.4.12, p. 339. *)
Theorem holomorphic_germ_directional_coefficients_injective (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) a
    (alpha beta:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a):
  (forall k v,@holomorphic_germ_directional_coefficient R X NX hNX a k alpha v=
    @holomorphic_germ_directional_coefficient R X NX hNX a k beta v) ->alpha=beta.
Proof.
move=>hEqual.
apply:(@holomorphic_germ_jets_injective R X NX (complex_norm_real hNX) a alpha beta)=>k.
have hForm:@HolomorphicGermForms.value R X NX hNX a k alpha=
    @HolomorphicGermForms.value R X NX hNX a k beta.
  apply:(@sform_polynomial_injective (ComplexScalars.C R) X (ComplexScalars.C R)^o k
    (@complex_scalar_characteristic_zero R)).
  apply:funext=>v;exact:hEqual k v.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R k
  (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)))=>u.
have hh:=congr1 (fun F:S_m X (ComplexScalars.C R)^o k=>F [tuple u i|i<k]) hForm.
rewrite !(@HolomorphicGermForms.laws R X NX hNX a k) in hh.
have hTuple:[ffun i=>tnth [tuple u j|j<k] i]=u.
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
by rewrite hTuple in hh.
Qed.
