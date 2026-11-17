(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),
    p. 326: actual original complex coordinate germs exist
    uniquely. The original paired real basis proves boundedness;
    actual holomorphic linear representatives remain local witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  ComplexOrderedBases LinearBasis NormOpenDomainLaws NormFiniteLinearBound HolomorphicLinear
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicGermRingLaws
  HolomorphicCoordinateGermsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coordinates.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation hNXR:=(complex_norm_real hNX).

(** Source for [holomorphic_coordinate_representative_exists]: every
    original complex coordinate has its original actual holomorphic
    representative, extending 3.4.8(1), p. 326. *)
Lemma holomorphic_coordinate_representative_exists j:
  exists f:@holomorphic_representative_type R X NX hNXR 0,
    forall x,holomorphic_representative_value f x=omega j x.
Proof.
have hBound:=@norm_finite_linear_bounded R XR CR NX (@complex_modulus R) hNXR
  (@complex_modulus_real_norm R) (n+n)%N (@ordered_real_basis R X n e)
  (@ordered_real_basisP R X n e he) (complex_hom_real (omega j)).
have hHolomorphic:=@holomorphic_bounded_linear R X (ComplexScalars.C R)^o NX (@complex_modulus R)
  hNXR (@complex_modulus_real_norm R) setT (omega j)
  (fun x _=>@norm_full_domain_interior R XR NX x) hBound.
have [f hValues]:=@holomorphic_representative_from_domain R X NX hNXR 0 setT (omega j) Logic.I hHolomorphic.
exists f=>x;by rewrite hValues.
Qed.

(** Source for [holomorphic_coordinate_germs_exist]: all original
    gamma_j exist with exactly their independent representative
    equations, extending corrected 3.4.8(1), p. 326. *)
Theorem holomorphic_coordinate_germs_exist:
  exists gamma:'I_n->@holomorphic_germ_ring R X NX hNXR 0,
    @is_holomorphic_coordinate_germs R X NX hNX n omega gamma.
Proof.
have [f hF]:=choice holomorphic_coordinate_representative_exists.
exists (fun j=>holomorphic_germ (f j))=>j g hG.
apply:holomorphic_germ_pointwise_equality=>x;by rewrite hG hF.
Qed.

(** Source for [holomorphic_coordinate_germs_unique]: the original
    coordinate equations determine each gamma_j uniquely, extending
    corrected 3.4.8(1), p. 326. *)
Lemma holomorphic_coordinate_germs_unique
    (gamma delta:'I_n->@holomorphic_germ_ring R X NX hNXR 0):
  @is_holomorphic_coordinate_germs R X NX hNX n omega gamma ->
  @is_holomorphic_coordinate_germs R X NX hNX n omega delta ->gamma=delta.
Proof.
move=>hGamma hDelta;apply:funext=>j.
have [f hValues]:=holomorphic_coordinate_representative_exists j.
by rewrite -(hGamma j f hValues) -(hDelta j f hValues).
Qed.
End Coordinates.
