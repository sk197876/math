(** Federer (1969), 3.4.5, p. 320: opaque
    set-germ ideals with the original local-vanishing laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP SetGermUP GermVanishingUP GermVanishingExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticSetIdealSignature.
(** Source for [value]: ideal gamma_a(S), 3.4.5,
    p. 320, determined by its set germ. *)
Parameter value:forall (R:realType) (X:lmodType R) (NX:X->R)
  (hNX:is_real_norm NX) (a:X),
  @set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a->set (analytic_germ_space hNX a).
(** Source for [laws]: the independent all-representative
    membership law, 3.4.5, p. 320. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R)
  (hNX:is_real_norm NX) (a:X) sigma,
  @is_analytic_set_ideal R X NX hNX a sigma (@value R X NX hNX a sigma).
End AnalyticSetIdealSignature.
Module AnalyticSetIdeal:AnalyticSetIdealSignature.
(** Source for [value]: private choice of the proved
    unique membership set, 3.4.5, p. 320. *)
Definition value (R:realType) (X:lmodType R) (NX:X->R)
    (hNX:is_real_norm NX) (a:X) sigma:=
  projT1 (cid (@analytic_set_ideal_exists R X NX hNX a sigma)).
(** Source for [laws]: the selected set satisfies the
    original vanishing law, 3.4.5, p. 320. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R)
    (hNX:is_real_norm NX) (a:X) sigma:
  @is_analytic_set_ideal R X NX hNX a sigma (@value R X NX hNX a sigma).
Proof. exact:(projT2 (cid (@analytic_set_ideal_exists R X NX hNX a sigma))). Qed.
End AnalyticSetIdeal.
