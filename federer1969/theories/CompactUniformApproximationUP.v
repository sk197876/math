(** Federer (1969), 4.1.5, p. 349: the uniform
    approximation and common compact support used in the
    extension argument. This independent predicate states
    those properties before any convolution family or
    extension functional is chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_uniform_test_approximation]:
    the common compact support and uniform limit of the
    original Phi_e*w in Federer 4.1.5, p. 349. Only
    positive scales matter, and every sufficiently small
    scale has support in one compact subset of U. *)
Definition is_compact_uniform_test_approximation (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (w:X->Y) (P:R->E):Prop:=
  exists C:set X,compact C /\ C `<=` U /\ exists r:R,0<r /\
    (forall e:R,0<e ->e<r ->forall x,~C x ->value (P e) x=0) /\
    (forall eta:R,0<eta ->exists d:R,0<d /\
      forall e:R,0<e ->e<d ->forall x,NY (value (P e) x-w x)<eta).
