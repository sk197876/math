(** Federer (1969), 3.1.21, p. 234: the inverse-adjoint
    ambient coordinate lift underlying the normal bundle. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_cotangent_lift]: the normal-bundle
    coordinate change (x,u) -> (f(x),D(f^-1)(f(x))^*u)
    underlying the normal bundle assertion of Federer 3.1.21,
    p. 234. The inverse derivative field E is supplied
    with actual differential laws in subsequent theorems. *)
Definition euclidean_cotangent_lift (R:realType) n
    (f:R_n R n->R_n R n) (E:R_n R n->Hom (R_n R n) (R_n R n))
    (z:R_n R (n+n)) : R_n R (n+n) :=
  @euclidean_first_injection_map R n n (f (@euclidean_first_block_map R n n z))+
  @euclidean_last_injection_map R n n
    (@euclidean_adjoint R n (E (f (@euclidean_first_block_map R n n z)))
      (@euclidean_last_block_map R n n z)).
