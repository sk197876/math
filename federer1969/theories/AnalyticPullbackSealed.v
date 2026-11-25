(** Federer (1969), 3.4.5, p. 319: opaque induced
    germ maps, exposed only through all original representative equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermUP
  AnalyticPullbackUP AnalyticPullbackExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type AnalyticPullbackSignature.
(** Source for [map]: the induced germ map, 3.4.5, p. 319. *)
Parameter map:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X),
  @norm_analytic_at R X Y NX NY hNX hNY A u a ->
  analytic_germ_space hNY (u a)->analytic_germ_space hNX a.
(** Source for [laws]: every original representative equation,
    3.4.5, p. 319, with no selected representative exposed. *)
Parameter laws:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
  (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X)
  (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a),
  is_analytic_germ_pullback hu (@map R X Y NX NY hNX hNY A u a hu).
End AnalyticPullbackSignature.
Module AnalyticPullback:AnalyticPullbackSignature.
(** Source for [map]: a private witness of the proved
    existence theorem, 3.4.5, p. 319. *)
Definition map (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X)
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a):=
  projT1 (cid (@analytic_germ_pullback_exists R X Y NX NY hNX hNY A u a hu)).
(** Source for [laws]: the selected witness satisfies the
    independent representative specification, 3.4.5, p. 319. *)
Lemma laws (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (u:X->Y) (a:X)
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a):
    is_analytic_germ_pullback hu (@map R X Y NX NY hNX hNY A u a hu).
Proof. exact:(projT2 (cid (@analytic_germ_pullback_exists R X Y NX NY hNX hNY A u a hu))). Qed.
End AnalyticPullback.
