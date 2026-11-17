(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    pointed coordinate pullbacks selected from proved existence
    and hidden behind their independent representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermUP
  PointedAnalyticPullbackUP PointedAnalyticPullbackExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type PointedAnalyticPullbackSignature.
(** Source for [map]: the original pointed coordinate
    map on germs, supporting 3.4.8(1),(5), pp. 326, 328. *)
Parameter map:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X) (b:Y),
  @norm_analytic_at R X Y NX NY hNX hNY A u a ->u a=b ->
  analytic_germ_space hNY b->analytic_germ_space hNX a.
(** Source for [laws]: every original representative
    equation, supporting 3.4.8(1),(5), pp. 326, 328. *)
Parameter laws:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X) (b:Y)
  (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a) (hab:u a=b),
  is_pointed_analytic_germ_pullback u (@map R X Y NX NY hNX hNY A u a b hu hab).
End PointedAnalyticPullbackSignature.
Module PointedAnalyticPullback:PointedAnalyticPullbackSignature.
(** Source for [map]: a private choice from proved
    existence, supporting 3.4.8(1),(5), pp. 326, 328. *)
Definition map (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X) (b:Y)
  (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a) (hab:u a=b):=
  projT1 (cid (@pointed_analytic_germ_pullback_exists R X Y NX NY hNX hNY A u a b hu hab)).
(** Source for [laws]: the hidden witness satisfies
    the independent equations of 3.4.8(1),(5), pp. 326, 328. *)
Lemma laws (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X) (b:Y)
  (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a) (hab:u a=b):
  is_pointed_analytic_germ_pullback u (@map R X Y NX NY hNX hNY A u a b hu hab).
Proof.
exact:(projT2 (cid (@pointed_analytic_germ_pullback_exists R X Y NX NY hNX hNY A u a b hu hab))).
Qed.
End PointedAnalyticPullback.
