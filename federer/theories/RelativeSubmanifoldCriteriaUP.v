(** Federer (1969), 3.1.22, pp. 235–236: the
    existential and universal retraction and coordinate criteria. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP RetractionUP PartialFunctionUP
  NormCoordinateSystemUP RelativeDifferentialUP ParametricDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Criteria.
Variable R:realType.
Variables X Z Y:lmodType R.
Variables (NX:X->R) (NZ:Z->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNZ:is_real_norm NZ).
Variables (B:set X) (f:X->Y) (a:X) (L:partial_function X Y).

(** Source for [relative_some_retraction_differential]: condition (2)
    of Federer 3.1.22, p. 235, with its actual
    neighbourhood retraction and restricted differential. *)
Definition relative_some_retraction_differential :=
  exists (T:set X) (r:X->X),norm_domain_interior NX T a /\
    is_norm_class_retraction hNX T (B `&` T) r 1%N /\
    exists M:Hom X Y,has_norm_differential NX NY T (fun x=>f (r x)) a M /\
      is_tangent_differential_restriction NX B a M L.

(** Source for [relative_every_retraction_differential]: condition [2]
    of Federer 3.1.22, p. 236: replace some by
    every in condition (2), retaining the same exact relative graph. *)
Definition relative_every_retraction_differential :=
  forall (T:set X) (r:X->X),norm_domain_interior NX T a ->
    is_norm_class_retraction hNX T (B `&` T) r 1%N ->
    exists M:Hom X Y,has_norm_differential NX NY T (fun x=>f (r x)) a M /\
      is_tangent_differential_restriction NX B a M L.

(** Source for [relative_some_coordinate_differential]: condition (3)
    of Federer 3.1.22, p. 235. The tangent-space
    inverse of Dpsi is expressed by the exact parametric graph. *)
Definition relative_some_coordinate_differential :=
  exists (T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) (E:Hom X Z) (J:Hom Z X),
    T a /\ is_norm_coordinate_system hNX hNZ B T V phi psi 1%N /\
    has_norm_differential NX NZ T phi a E /\
    has_norm_differential NZ NX V psi (phi a) J /\
    exists Q:Hom Z Y,has_norm_differential NZ NY V (fun u=>f (psi u)) (phi a) Q /\
      is_parametric_differential_restriction J Q L.

(** Source for [relative_every_coordinate_differential]: condition [3]
    of Federer 3.1.22, p. 236: every class-one
    coordinate system gives the same relative differential. *)
Definition relative_every_coordinate_differential :=
  forall (T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) (E:Hom X Z) (J:Hom Z X),
    T a -> is_norm_coordinate_system hNX hNZ B T V phi psi 1%N ->
    has_norm_differential NX NZ T phi a E ->
    has_norm_differential NZ NX V psi (phi a) J ->
    exists Q:Hom Z Y,has_norm_differential NZ NY V (fun u=>f (psi u)) (phi a) Q /\
      is_parametric_differential_restriction J Q L.
End Criteria.
