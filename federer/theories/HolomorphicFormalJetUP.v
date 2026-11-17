(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: independently specify the actual symmetric complex
    scalar laws and factorial bounds of a coefficient sequence.
    Realisation and compactness are conclusions to prove. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  ComplexScalarSlotUP ContinuousMultilinearUP ContinuousMultilinearSealed FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Jets.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNXR hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNXR hN).
Local Notation NZ:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNXR hN).

(** Source for [is_holomorphic_formal_jet]: the original coefficient
    symmetry, factorial bounds and additional complex scalar laws,
    extending 3.4.5, p. 319. No existence theorem enters
    this specification, including at degree zero. *)
Record is_holomorphic_formal_jet (s t:nat) (w:forall m,Z m):Prop:={
  (** Source for [holomorphic_formal_jet_symmetric]: the original
      derivative symmetry, 3.1.11, p. 220, under 3.4.12, p. 338. *)
  holomorphic_formal_jet_symmetric:forall m (sigma:'S_m) u,
    ev m (finite_argument_permutation sigma u) (w m)=ev m u (w m);
  (** Source for [holomorphic_formal_jet_growth]: the exact original
      all-order factorial bound, extending 3.4.5, p. 319. *)
  holomorphic_formal_jet_growth:forall m,NZ m (w m)<=s%:R*t%:R^+m*(m`!)%:R;
  (** Source for [holomorphic_formal_jet_complex]: the actual complex
      slot equations of 3.4.12, p. 338, in every degree. *)
  holomorphic_formal_jet_complex:forall m,has_complex_scalar_slot_laws (fun u=>ev m u (w m))
}.
End Jets.
