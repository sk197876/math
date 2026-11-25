(** Federer (1969), 3.4.5, p. 319: opaque actual
    germ derivatives with independent representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsUP AnalyticGermJetExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Module Type AnalyticGermJetsSignature.
(** Source for [value]: the actual m-th differential of
    an analytic germ, 3.4.5, p. 319. *)
Parameter value:forall (R:realType) (X:lmodType R) (NX:X->R)
  (hNX:is_real_norm NX) (a:X) m,analytic_germ_space hNX a->
  @ContinuousMultilinear.space R m X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R).
(** Source for [laws]: the actual differential at the centre
    of every original representative, 3.4.5, p. 319. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R)
  (hNX:is_real_norm NX) (a:X) m (alpha:analytic_germ_space hNX a),
  is_analytic_germ_jet alpha (@value R X NX hNX a m alpha).
End AnalyticGermJetsSignature.
Module AnalyticGermJets:AnalyticGermJetsSignature.
(** Source for [value]: private choice of the unique jet
    whose existence was proved, 3.4.5, p. 319. *)
Definition value (R:realType) (X:lmodType R) (NX:X->R)
    (hNX:is_real_norm NX) (a:X) m (alpha:analytic_germ_space hNX a):=
  projT1 (cid (@analytic_germ_jet_exists R X NX hNX a m alpha)).
(** Source for [laws]: the selected jet satisfies the
    independent all-representative laws, 3.4.5, p. 319. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R)
    (hNX:is_real_norm NX) (a:X) m (alpha:analytic_germ_space hNX a):
  is_analytic_germ_jet alpha (@value R X NX hNX a m alpha).
Proof. exact:(projT2 (cid (@analytic_germ_jet_exists R X NX hNX a m alpha))). Qed.
End AnalyticGermJets.
