(** Federer (1969), 3.4.12, p. 339, extending 3.4.6, p. 322: an opaque
    transverse normed space, exposed only through the original
    kernel, splitting, inherited-norm and boundedness laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus HolomorphicLinear
  ComplexWeierstrassTransverseUP ComplexWeierstrassTransverseExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type ComplexWeierstrassTransverseSignature.
(** Source for [space]: the actual kernel carrier,
    3.4.6, pp. 322–323. *)
Parameter space:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
  (v:X) (xi:Hom X (ComplexScalars.C R)^o) (hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_hom_real xi)) (hUnit:xi v= 1),
  lmodType (ComplexScalars.C R).
(** Source for [norm]: the inherited kernel norm,
    3.4.6, pp. 322–323. *)
Parameter norm:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
  (v:X) (xi:Hom X (ComplexScalars.C R)^o) (hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_hom_real xi)) (hUnit:xi v= 1),
  @space R X NX hNX v xi hXi hUnit->R.
(** Source for [norm_laws]: the inherited norm laws,
    3.4.6, pp. 322–323. *)
Parameter norm_laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
  (v:X) (xi:Hom X (ComplexScalars.C R)^o) (hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_hom_real xi)) (hUnit:xi v= 1),
  is_complex_norm (@norm R X NX hNX v xi hXi hUnit).
(** Source for [inclusion]: the actual kernel inclusion,
    3.4.6, pp. 322–323. *)
Parameter inclusion:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
  (v:X) (xi:Hom X (ComplexScalars.C R)^o) (hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_hom_real xi)) (hUnit:xi v= 1),
  Hom (@space R X NX hNX v xi hXi hUnit) X.
(** Source for [projection]: the original transverse projection,
    3.4.6, pp. 322–323. *)
Parameter projection:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
  (v:X) (xi:Hom X (ComplexScalars.C R)^o) (hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_hom_real xi)) (hUnit:xi v= 1),
  Hom X (@space R X NX hNX v xi hXi hUnit).
(** Source for [laws]: the original splitting equations and bounds,
    3.4.6, pp. 322–323. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
  (v:X) (xi:Hom X (ComplexScalars.C R)^o) (hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_hom_real xi)) (hUnit:xi v= 1),
  is_complex_weierstrass_transverse_space NX (@norm R X NX hNX v xi hXi hUnit) v xi
  (@inclusion R X NX hNX v xi hXi hUnit) (@projection R X NX hNX v xi hXi hUnit).
End ComplexWeierstrassTransverseSignature.
Module ComplexWeierstrassTransverse:ComplexWeierstrassTransverseSignature.
Section Parameters.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variable hXi:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_hom_real xi).
Variable hUnit:xi v= 1.
Let witness:=cid (@complex_weierstrass_transverse_space_exists R X NX hNX v xi hXi hUnit).
(** Source for [space]: select a private carrier from the
    proved transverse existence theorem, 3.4.6, p. 322. *)
Definition space:lmodType (ComplexScalars.C R):=projT1 witness.
Let norm_witness:=cid (projT2 witness).
(** Source for [norm]: select the proved inherited norm,
    3.4.6, pp. 322–323. *)
Definition norm:space->R:=projT1 norm_witness.
(** Source for [norm_laws]: the selected norm satisfies
    the actual norm laws, 3.4.6, pp. 322–323. *)
Lemma norm_laws:is_complex_norm norm.
Proof. exact:(projT2 norm_witness).1. Qed.
Let inclusion_witness:=cid (projT2 norm_witness).2.
(** Source for [inclusion]: select the proved kernel
    inclusion, 3.4.6, p. 322. *)
Definition inclusion:Hom space X:=projT1 inclusion_witness.
Let projection_witness:=cid (projT2 inclusion_witness).
(** Source for [projection]: select the original eta
    projection from its existence proof, 3.4.6, p. 322. *)
Definition projection:Hom X space:=projT1 projection_witness.
(** Source for [laws]: all original splitting laws hold
    for the selected witnesses, 3.4.6, pp. 322–323. *)
Lemma laws:is_complex_weierstrass_transverse_space NX norm v xi inclusion projection.
Proof. exact:(projT2 projection_witness). Qed.
End Parameters.
End ComplexWeierstrassTransverse.
