(** Supporting Federer (1969), 3.4.8(5), p. 328:
    actual finite derivative prefixes behind their opaque
    coordinate interface. No representation is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticFiniteJetsUP AnalyticFiniteJetsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticFiniteJetsSignature.
(** Source for [map]: the original finite derivative
    prefix, supporting 3.4.8(5), p. 328, and
    specified by 3.4.5, p. 319. *)
Parameter map:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) m a,
  @analytic_germ_ring R X NX hNX a->@analytic_finite_jet_space R X NX hNX m.
(** Source for [laws]: every coordinate is the
    actual derivative, supporting the same source assertions. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) m a,
  is_analytic_finite_jet_map (@map R X NX hNX m a).
End AnalyticFiniteJetsSignature.
Module AnalyticFiniteJets:AnalyticFiniteJetsSignature.
(** Source for [map]: a hidden witness of proved
    existence, supporting 3.4.8(5), p. 328. *)
Definition map (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) m a:=
  projT1 (cid (@analytic_finite_jet_map_exists R X NX hNX m a)).
(** Source for [laws]: the hidden map satisfies
    the independent actual-derivative laws, 3.4.8(5), p. 328. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) m a:
  is_analytic_finite_jet_map (@map R X NX hNX m a).
Proof. exact:(projT2 (cid (@analytic_finite_jet_map_exists R X NX hNX m a))). Qed.
End AnalyticFiniteJets.
