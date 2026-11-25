(** Federer (1969), 3.2.28(4), printed p. 267:
    G(n,m) is identified with the squares of unit simple
    m-vectors. Specify the actual plane association and
    symmetric-square value before proving this realization. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP ModuleQuotient GrassmannSubspaces AssociatedSubspace
  ExteriorGrading ExteriorNorm SymmetricGrading SymmetricSquareGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_grassmann_square_representative]: the
    identification of G(n,m) with T(Go(n,m)) in Federer
    3.2.28(4), p. 267, using the associated plane
    of 1.6.2, p. 24. Both the unit exterior vector
    and its exact plane and square are proof obligations. *)
Definition is_grassmann_square_representative (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (h2:(1+1:R)!=0) m
    (P:G V m) (t:symmetric_power (exterior_power V m) 2):=
  exists x:exterior_power V m,
    simple x /\exterior_norm h2 hB x= 1 /\
    (forall v,grassmann_val P v <->FedererSimple.T x v) /\
    inner_projective_square x=t.
