(** Federer (1969), 3.4.12, pp. 338–339:
    actual original holomorphic germ jets are complex
    multilinear. Reuse the full higher-differential theorem
    and original representative independence; norm-proof conversions
    use only the existing proof-irrelevance law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm TensorFamilyUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialLocal HolomorphicUP HolomorphicOpenDomain
  HolomorphicHigherComplexMultilinear HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws HolomorphicGermJetsUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Jets.
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
Variable alpha:holomorphic_germ_space hNXR a.

(** Source for [holomorphic_germ_positive_jet_complex]: the
    actual original positive-order germ derivatives are complex
    multilinear, as asserted in 3.4.12, p. 338.
    No representative, extra vanishing law or higher complex
    linearity hypothesis enters the statement. *)
Theorem holomorphic_germ_positive_jet_complex k:
  @multilinear C k.+1 (fun _=>X) C^o
    (fun u=>@ev k.+1 u (@HolomorphicGermJets.value R X NX hNXR a k.+1 alpha)).
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNXR a alpha.
have [U [ha hF]]:=holomorphic_representative_holomorphic f.
pose z:=@HolomorphicGermJets.value R X NX hNXR a k.+1 alpha.
have hFull:=@HolomorphicGermJets.laws R X NX hNXR a k.+1 alpha f hf.
have hOpen:=@holomorphic_domain_interior R X C^o NX NC hNXR hNC U
  (holomorphic_representative_value f) hF.
have hLocal:=(@norm_higher_differential_open_restriction R XR CR NX NC hNXR hNC
  Z ev ZN hZ k.+1 setT U (holomorphic_representative_value f)
  (fun x _=>Logic.I) hOpen a ha z).1 hFull.
have hGeneral:=@holomorphic_higher_complex_multilinear R X C^o NX NC
  hNX (@complex_modulus_complex_norm R).
have hProof:(complex_norm_real (@complex_modulus_complex_norm R))=hNC:=Prop_irrelevance _ _.
rewrite hProof in hGeneral.
exact:(hGeneral U (holomorphic_representative_value f) k a z hF hLocal).
Qed.

(** Source for [holomorphic_germ_jet_complex]: include
    the original zeroth coefficient alongside all positive
    complex multilinear jets, 3.4.12, pp. 338–339.
    The empty tuple has no scalar slot to constrain. *)
Theorem holomorphic_germ_jet_complex k:
  @multilinear C k (fun _=>X) C^o
    (fun u=>@ev k u (@HolomorphicGermJets.value R X NX hNXR a k alpha)).
Proof.
case:k=>[|k];last exact:holomorphic_germ_positive_jet_complex.
move=>u i;have hi:=ltn_ord i;by rewrite ltn0 in hi.
Qed.
End Jets.
