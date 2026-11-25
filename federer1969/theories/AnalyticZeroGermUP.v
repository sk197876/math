(** Federer (1969), 3.4.5, p. 320: the
    variety germ of one actual analytic equation depends
    only on its analytic germ. This independent law is
    used for the ideal and irreducibility assertions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP SetGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_zero_germ]: every original
    representative gives the same zero-set germ, supporting
    var(I) and irreducibility in 3.4.5, p. 320. *)
Definition is_analytic_zero_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:analytic_germ_space hNX a)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):=
  forall f:@analytic_representative_type R X NX hNX a,analytic_germ f=alpha ->
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) a
      [set x|analytic_representative_value f x=0]=sigma.
