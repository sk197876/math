(** Federer (1969), Corollary 2.8.15, p. 150: a centered fine family of
    small closed balls is adequate for a separable directionally limited
    target. Apply 2.8.2 with the singleton target family and sigma=2 zeta/(2
    zeta+1). The hypotheses here retain Federer's standing covering context
    and strict small-radius convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground CoveringFamilyUP ContractionCoverUP
  CoverContractionCriterion DirectionalLimitationUP CenteredBallCoverUP
  CenteredBallFineness FiniteCoverContraction CenteredCoverContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [singleton_target_contraction_adequacy]: the use of 2.8.2
    with K={A} in Federer 2.8.15, p. 150 A supporting specialization of the
    already proved theorem, with no target-measurability or
    finite-target-measure premise. *)
Lemma singleton_target_contraction_adequacy (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (F : set (set X)) (A : set X) (sigma : R) :
  is_covering_theory_context F phi -> 0 < sigma < 1 ->
  has_local_cover_contraction phi F A sigma -> family_is_measure_adequate phi F A.
Proof.
move=> hc hs hl.
have hlocal (B : {T : set X | [set A] T}) : has_local_cover_contraction phi F (sval B) sigma.
  have he : sval B = A := svalP B; by rewrite he.
have h := @federer_2_8_2 R X F [set A] phi (fun _ => sigma) hc (countable1 A)
  (fun _ => hs) hlocal.
by rewrite bigcup_set1 in h.
Qed.

(** Source for [centered_ball_contraction_factor]: the printed
    sigma=2 zeta/(2 zeta+1) in Federer 2.8.15, p. 150.
    This identifies the loss factor derived from a finite cover
    with the exact fraction used in the book. *)
Lemma centered_ball_contraction_factor (R : realType) (zeta : nat) :
  finite_cover_loss_factor R (2*zeta+1)%N = (2*zeta)%:R/(2*zeta+1)%:R.
Proof. by rewrite addn1 finite_cover_loss_factor_succ. Qed.

(** Source for [federer_2_8_15]: the complete corollary in
    Federer 2.8.15, p. 150. Under the inherited small-ball
    and directional hypotheses and the standing measure context,
    separability of A and zero centered-radius infima imply
    adequacy of F for A. The proof uses the printed contraction
    fraction, and requires no measurability of the target A. *)
Theorem federer_2_8_15 (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (F : set (set X)) (A : set X)
    (xi : \bar R) (eta mu : R) (zeta : nat) :
  is_covering_theory_context F phi -> is_directionally_limited_at A xi eta zeta ->
  0 < mu -> (mu%:E < (1/2 : R)%:E * xi)%E ->
  is_small_closed_ball_family mu F ->
  (exists D : set (metric_subset A), countable D /\ dense D) ->
  has_zero_centered_radius_infimum F A -> family_is_measure_adequate phi F A.
Proof.
move=> hc hlim hm hsmall _ hsep hinf.
have hf := (centered_radius_infimum_zero_iff_small_balls F A).1 hinf.
have hlocal := @centered_fine_cover_local_contraction R X phi F A xi eta mu zeta
  hc hlim hm hsmall hsep hf.
have hZ := directional_cardinal_positive hlim.
have htwo : (0 < 2*zeta)%N by rewrite muln_gt0 hZ.
have hN : (1 < 2*zeta+1)%N by rewrite addn1 ltnS.
have hs := @finite_cover_loss_factor_range R (2*zeta+1)%N hN.
exact: singleton_target_contraction_adequacy hc hs hlocal.
Qed.
