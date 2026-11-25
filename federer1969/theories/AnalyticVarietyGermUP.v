(** Federer (1969), 3.4.5, pp. 320–321:
    analytic variety germs and the original local analytic-set
    condition. The definitions retain their actual domain and
    equation requirements and include no decomposition theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP FiniteAnalyticVarietyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_variety_germ]: the germs of
    finite analytic subvarieties of neighbourhoods of a,
    forming V_a(X), 3.4.5, p. 320. *)
Definition is_analytic_variety_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):Prop:=
  exists U S:set X,U a /\is_finite_analytic_variety hNX U S /\
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) a S=alpha.

(** Source for [is_analytic_set_in]: the germwise
    definition of S analytic in A, 3.4.5, p. 321.
    The original S and A are arbitrary subsets. *)
Definition is_analytic_set_in (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A S:set X):Prop:=
  forall a,A a ->@is_analytic_variety_germ R X NX hNX a
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S).

(** Source for [has_local_analytic_variety_cover]: the
    equivalent open-cover condition in 3.4.5, p. 321.
    An open set around each original point has exactly
    the original local intersection as a finite analytic variety. *)
Definition has_local_analytic_variety_cover (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A S:set X):Prop:=
  forall a,A a ->exists U:set X,U a /\is_finite_analytic_variety hNX U (U `&` S).
