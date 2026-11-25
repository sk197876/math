(** Federer (1969), 3.1.11, p. 220:
    continuous bilinear operations on normed spaces,
    including composition of continuous linear maps.
    The homogeneous product bound expresses continuity
    using only the supplied norms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_bounded_bilinear]: supporting
    intrinsic specification of the continuous bilinear
    operations used in the higher-calculus induction of
    Federer 3.1.11, p. 220. Boundedness
    is a property to prove, not a project axiom. *)
Definition norm_bounded_bilinear (R : realType)
    (U V W : lmodType R) (NU : U->R) (NV : V->R) (NW : W->R)
    (B : U->V->W) :=
  bilinear B /\ exists C : R, 0<=C /\
    forall u v, NW (B u v)<=C*(NU u*NV v).
