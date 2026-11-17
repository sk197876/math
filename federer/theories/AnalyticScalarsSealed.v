(** Federer (1969), 3.4.8(1),(8), pp. 326, 329:
    the original scalar homomorphism behind the
    exact opaque constant-representative law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticScalarsUP AnalyticScalarsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticScalarsSignature.
(** Source for [map]: the original scalar constants
    as actual analytic germs, 3.4.8(1), p. 326. *)
Parameter map:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a,
  {rmorphism R->@analytic_germ_ring R X NX hNX a}.
(** Source for [laws]: every original scalar has its
    exact constant-function representative,
    3.4.8(1),(8), pp. 326, 329. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a,
  is_analytic_scalar_map (@map R X NX hNX a).
End AnalyticScalarsSignature.
Module AnalyticScalars:AnalyticScalarsSignature.
(** Source for [map]: private choice from the proved
    original scalar existence theorem,
    3.4.8(1),(8), pp. 326, 329. *)
Definition map (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a:
  {rmorphism R->@analytic_germ_ring R X NX hNX a}:=
  projT1 (cid (@analytic_scalar_map_exists R X NX hNX a)).
(** Source for [laws]: the private homomorphism satisfies
    the independent original representative equation,
    3.4.8(1),(8), pp. 326, 329. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) a:
  is_analytic_scalar_map (@map R X NX hNX a).
Proof. exact:(projT2 (cid (@analytic_scalar_map_exists R X NX hNX a))). Qed.
End AnalyticScalars.
