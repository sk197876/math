(** Federer (1969), 3.4.12, p. 338: the actual real
    differential of a holomorphic map is complex linear. Connect
    any already checked real differential to its complex carrier,
    using the defining scalar law and the existing map adapter. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  NormDifferentialUP HolomorphicUP HolomorphicLinear ComplexRealLinearMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_actual_differential_complex_restriction]:
    complex linearity in the original definition of holomorphy,
    3.4.12, p. 338. The given real differential remains exactly
    the restriction of the resulting complex map. This is an
    interface connection, with no new analytic argument. *)
Theorem holomorphic_actual_differential_complex_restriction (R:realType)
    (X Y:lmodType (ComplexScalars.C R)) (NX:X->R) (NY:Y->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (f:X->Y) a
    (L:Hom (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) Y)):
  @is_holomorphic R X Y NX NY hNX hNY A f ->
  @has_norm_differential R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) Y) NX NY A f a L ->
  exists D:Hom X Y,complex_hom_real D=L.
Proof.
move=>hF hL.
have ha:=norm_domain_interior_member hNX (norm_differential_interior hL).
have hComplex:=hF.2 a L ha hL.
have [D hValues]:=complex_real_linear_map_exists hComplex.
exists D;apply:hom_ext=>x;exact:hValues x.
Qed.
