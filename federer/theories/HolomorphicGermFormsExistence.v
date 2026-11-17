(** Federer (1969), 3.4.12, pp. 338–339:
    actual original germ differentials have unique complex
    symmetric-form carriers. Apply the existing family-to-tuple
    theorem to the proved complex multilinearity and actual
    derivative symmetry; do not construct a new form algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm SymmetricForms MultilinearTupleForm ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialSymmetry HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermJetsSealed
  HolomorphicGermJetsComplex HolomorphicGermFormsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Forms.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k XR CR NX NC hNXR hNC).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k XR CR NX NC hNXR hNC).
Local Notation ZN:=(fun k=>@ContinuousMultilinear.norm R k XR CR NX NC hNXR hNC).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k XR CR NX NC hNXR hNC).
Variable a:X.

(** Source for [holomorphic_germ_form_exists]: the original
    actual complex symmetric coefficient exists in every
    order, including zero, 3.4.12, pp. 338–339. *)
Theorem holomorphic_germ_form_exists k (alpha:holomorphic_germ_space hNXR a):
  exists F:S_m X C^o k,@is_holomorphic_germ_form R X NX hNX a k alpha F.
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNXR a alpha.
pose z:=@HolomorphicGermJets.value R X NX hNXR a k alpha.
have hActual:=@HolomorphicGermJets.laws R X NX hNXR a k alpha f hf.
have hSymmetry:=@norm_higher_differential_symmetric R XR CR NX NC hNXR hNC
  Z ev ZN hZ setT (holomorphic_representative_value f) k a z hActual.
exact:(@symmetric_multilinear_tuple_form_exists C X C^o k (fun u=>@ev k u z)
  (@holomorphic_germ_jet_complex R X NX hNX a alpha k) hSymmetry).
Qed.

(** Source for [holomorphic_germ_form_unique]: the original
    all-tuple jet equation determines the complex form
    uniquely, 3.4.12, pp. 338–339. *)
Theorem holomorphic_germ_form_unique k (alpha:holomorphic_germ_space hNXR a)
    (F G:S_m X C^o k):
  @is_holomorphic_germ_form R X NX hNX a k alpha F ->@is_holomorphic_germ_form R X NX hNX a k alpha G ->F=G.
Proof. move=>hF hG;apply:sform_ext=>t;by rewrite hF hG. Qed.
End Forms.
