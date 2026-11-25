(** Federer (1969), 4.1.1, p. 344: independent meanings of
    a topological vector space and local convexity. These laws
    are proved for E(U,Y); they are not imposed on Federer's
    final topology on D(U,Y). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_family_jointly_continuous]: the ordinary
    open-rectangle criterion for continuity of two-variable maps,
    supporting the vector topology of Federer 4.1.1, p. 344. *)
Definition open_family_jointly_continuous (X Y Z:Type)
    (O:set (set X)) (P:set (set Y)) (Q:set (set Z)) (f:X->Y->Z) :=
  forall x y A,Q A -> A (f x y) -> exists B C,
    O B /\ P C /\ B x /\ C y /\
    forall u v,B u -> C v -> A (f u v).

(** Source for [is_open_vector_topology]: continuity of vector
    addition and real scalar multiplication, supporting the
    topological-vector-space assertion in Federer 4.1.1, p. 344.
    Absolute-value intervals describe the usual scalar topology. *)
Record is_open_vector_topology (R:realType) (E:lmodType R)
    (O:set (set E)) : Prop := {
  (** Source for [open_vector_topology]: the underlying open-set
      topology, Federer 4.1.1, p. 344. *)
  open_vector_topology : is_open_family_topology O;
  (** Source for [open_vector_addition]: joint continuity of
      addition, supporting Federer 4.1.1, p. 344. *)
  open_vector_addition : open_family_jointly_continuous O O O (fun x y=>x+y);
  (** Source for [open_vector_scaling]: joint continuity of real
      scalar multiplication, supporting Federer 4.1.1, p. 344. *)
  open_vector_scaling : forall c x A,O A -> A (c*:x) ->
    exists d B,0<d /\ O B /\ B x /\
      forall s y,`|s-c|<d -> B y -> A (s*:y)
}.

(** Source for [open_family_locally_convex]: convex neighbourhoods
    of zero form a neighbourhood base, as asserted for E(U,Y)
    in Federer 4.1.1, p. 344. *)
Definition open_family_locally_convex (R:realType) (E:lmodType R)
    (O:set (set E)) := forall A,open_family_neighbourhood O 0 A ->
  exists B,open_family_neighbourhood O 0 B /\ B `<=` A /\
    forall x y,B x -> B y -> forall t:R,0<=t -> t<=1 ->
      B ((1-t)*:x+t*:y).

(** Source for [open_family_hausdorff]: distinct points have
    disjoint open neighbourhoods, the Hausdorff condition in
    Federer 4.1.1, p. 344. *)
Definition open_family_hausdorff (X:Type) (O:set (set X)) :=
  forall x y,x<>y -> exists A B,O A /\ O B /\ A x /\ B y /\
    forall z,~(A z /\ B z).
