(** Federer (1969), 3.4.5, p. 321: every
    nonempty family of analytic variety germs has a minimal
    member when the original analytic germ ring is Noetherian. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermRing SetGermUP SetGermOrder
  CommutativeIdealUP NoetherianIdealMaximum GermVanishingSealed GermVanishingIdeal GermVanishingMonotonicity
  AnalyticVarietyGermUP AnalyticVarietyGermSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [noetherian_analytic_variety_family_minimum]:
    the first assertion of 3.4.5, p. 321,
    under exactly its stated Noetherian hypothesis. Actual
    ideals reverse and detect containment of original analytic
    variety germs. *)
Theorem noetherian_analytic_variety_family_minimum (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (H:set (@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)):
  is_noetherian_commutative_ring [the comNzRingType of (@analytic_germ_ring R X NX hNX a)] ->
  (exists alpha,H alpha) ->
  (forall alpha,H alpha ->@is_analytic_variety_germ R X NX hNX a alpha) ->
  exists alpha,H alpha /\forall beta,H beta ->set_germ_subset beta alpha ->set_germ_subset alpha beta.
Proof.
move=>hNoetherian [alpha0 hAlpha0] hVarieties.
pose A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
pose ideal:=@AnalyticSetIdeal.value R X NX hNX a.
pose F:set (set A):=fun I=>exists alpha,H alpha /\I=ideal alpha.
have hFNonempty:exists I,F I by exists (ideal alpha0),alpha0;split.
have hFIdeals I:F I ->is_commutative_ideal I.
  move=>[alpha [hAlpha ->]];exact:(@analytic_set_ideal_ring_laws R X NX hNX a alpha).
have [I [[alpha [hAlpha hI]] hMax]]:=@noetherian_ideal_family_maximum A F hNoetherian hFNonempty hFIdeals.
exists alpha;split;first exact:hAlpha.
move=>beta hBeta hContainment.
have hIContained:I `<=` ideal beta.
  rewrite hI;exact:(@analytic_set_ideal_antitone R X NX hNX a beta alpha hContainment).
have hBetaFamily:F (ideal beta) by exists beta;split.
have hReverse:=hMax (ideal beta) hBetaFamily hIContained.
rewrite hI in hReverse.
exact:(@analytic_variety_germ_ideal_separation R X NX hNX a beta alpha (hVarieties beta hBeta) hReverse).
Qed.
