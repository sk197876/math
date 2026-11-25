(** Federer (1969), 3.4.12, p. 339:
    holomorphic variety germs and the original local holomorphic-set
    condition. The definitions retain their actual domain and
    equation requirements and include no decomposition theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric SetGermUP FiniteHolomorphicVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_variety_germ]: the germs of
    finite holomorphic subvarieties of neighbourhoods of a,
    forming V_a(X), 3.4.12, p. 339. *)
Definition is_holomorphic_variety_germ (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):Prop:=
  exists U S:set X,U a /\is_finite_holomorphic_variety hNX U S /\
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) a S=alpha.

(** Source for [is_holomorphic_set_in]: the germwise
    definition of S holomorphic in A, 3.4.12, p. 339.
    The original S and A are arbitrary subsets. *)
Definition is_holomorphic_set_in (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (A S:set X):Prop:=
  forall a,A a ->@is_holomorphic_variety_germ R X NX hNX a
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S).

(** Source for [has_local_holomorphic_variety_cover]: the
    equivalent open-cover condition in 3.4.12, p. 339.
    An open set around each original point has exactly
    the original local intersection as a finite holomorphic variety. *)
Definition has_local_holomorphic_variety_cover (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (A S:set X):Prop:=
  forall a,A a ->exists U:set X,U a /\is_finite_holomorphic_variety hNX U (U `&` S).
