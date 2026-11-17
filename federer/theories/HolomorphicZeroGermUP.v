(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: the
    variety germ of one actual analytic equation depends
    only on its analytic germ. This independent law is
    used for the ideal and irreducibility assertions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP SetGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_zero_germ]: every original
    representative gives the same zero-set germ, supporting
    var(I) and irreducibility in 3.4.5, p. 320. *)
Definition is_holomorphic_zero_germ (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (alpha:holomorphic_germ_space hNX a)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):=
  forall f:@holomorphic_representative_type R X NX hNX a,holomorphic_germ f=alpha ->
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) a
      [set x|holomorphic_representative_value f x=0]=sigma.
