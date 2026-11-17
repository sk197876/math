(** Federer (1969), 3.4.12, pp. 338–339: original linear
    coordinates on a finite-dimensional complex source are holomorphic.
    Reuse the original paired real basis, finite-source boundedness
    and the actual bounded-linear holomorphy theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexOrderedBases
  LinearBasis NormFiniteLinearBound NormOpenDomainLaws HolomorphicUP HolomorphicLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_complex_linear_holomorphic]: every original
    complex linear map on a finite-dimensional source is holomorphic
    on its whole source, extending the coordinate maps of
    3.4.8(1), p. 326. The target may have arbitrary dimension. *)
Theorem finite_complex_linear_holomorphic (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    n (e:'I_n->X) (he:is_basis e) (L:Hom X Y):
  is_holomorphic hNX hNY setT L.
Proof.
apply:(@holomorphic_bounded_linear R X Y NX NY hNX hNY setT L
  (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX x)).
exact:(@norm_finite_linear_bounded R (restricted_space (ComplexScalars.embed R) X)
  (restricted_space (ComplexScalars.embed R) Y) NX NY hNX hNY
  (n+n)%N (@ordered_real_basis R X n e) (@ordered_real_basisP R X n e he) (complex_hom_real L)).
Qed.
