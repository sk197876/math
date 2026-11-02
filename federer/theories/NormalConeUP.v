(** Federer (1969), 3.1.21, p. 234: normal cones and normal
    bundles in an arbitrary inner-product space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_normal_cone]: Nor(S,a) is the set of
    u with u.v<=0 for every v in Tan(S,a), Federer 3.1.21,
    p. 234. The inner product and its associated norm are
    supplied abstractly; no nearest-point construction is used. *)
Definition inner_normal_cone (R:realType) (X:lmodType R)
    (N:X->R) (B:X->X->R) (S:set X) a : set X :=
  fun u=>forall v,norm_tangent_cone N S a v -> B u v<=0.

(** Source for [inner_normal_bundle]: Nor(S)=(S times X)
    intersect {(a,u):u in Nor(S,a)}, Federer 3.1.21, p. 234.
    Its manifold dimension and regularity require a later theorem. *)
Definition inner_normal_bundle (R:realType) (X:lmodType R)
    (N:X->R) (B:X->X->R) (S:set X) : set (X*X) :=
  fun au=>S au.1 /\ inner_normal_cone N B S au.1 au.2.
