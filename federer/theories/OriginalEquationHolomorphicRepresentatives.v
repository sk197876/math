(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331:
    the actual defining functions represent
    the original finite algebraic generators.
    Apply the public representative equations
    for germ ring operations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP HolomorphicGermSealed RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [original_equation_holomorphic_representatives]:
    gamma_0(f_(m+1))=J(W) and
    gamma_0(f_j)=delta gamma_j-J(T_j),
    3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331.
    Both the exact function values and
    their germ ring equations are retained. *)
Theorem original_equation_holomorphic_representatives (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) (index:eqType) (first:index)
    (w d:@holomorphic_representative_type R X NX hNX a)
    (v t:index->@holomorphic_representative_type R X NX hNX a):
  exists f:index->@holomorphic_representative_type R X NX hNX a,
    (forall j x,holomorphic_representative_value (f j) x = if j==first then
      holomorphic_representative_value w x else
      holomorphic_representative_value d x*holomorphic_representative_value (v j) x-
        holomorphic_representative_value (t j) x) /\
    forall j,(holomorphic_germ (f j):[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]) =
      if j==first then (holomorphic_germ w:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]) else
      (holomorphic_germ d:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])*
        (holomorphic_germ (v j):[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])-
        (holomorphic_germ (t j):[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]).
Proof.
pose f:=fun j:index=>if j==first then w else
  @holomorphic_add_representatives R X NX hNX a
    (@holomorphic_multiply_representatives R X NX hNX a d (v j))
    (@holomorphic_negate_representative R X NX hNX a (t j)).
exists f;split.
- move=>j x;rewrite /f;case:(j==first);by [].
- move=>j;rewrite /f;case hCase:(j==first);first by [].
  by rewrite -(holomorphic_germ_add_equation (@HolomorphicGerms.laws R X NX hNX a))
    -(holomorphic_germ_multiply_equation (@HolomorphicGerms.laws R X NX hNX a))
    -(holomorphic_germ_negate_equation (@HolomorphicGerms.laws R X NX hNX a)).
Qed.
