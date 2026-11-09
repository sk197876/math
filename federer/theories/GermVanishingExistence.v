(** Federer (1969), 3.4.5, p. 320: the
    original all-representative vanishing law determines a unique
    subset of the analytic-germ ring. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP SetGermUP GermVanishingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_set_ideal_exists]: existence of
    the original ideal membership set, 3.4.5, p. 320.
    Its algebraic ideal laws are proved separately. *)
Theorem analytic_set_ideal_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  exists I:set (analytic_germ_space hNX a),is_analytic_set_ideal sigma I.
Proof.
exists (fun alpha=>forall (f:@analytic_representative_type R X NX hNX a)
  (S:set (Topological.clone (real_norm_metric_space hNX) _)),
  analytic_germ f=alpha ->@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S=sigma ->
  @vanishes_near_on (Topological.clone (real_norm_metric_space hNX) _) [the zmodType of R^o] a S (analytic_representative_value f)).
constructor=>alpha;by split.
Qed.

(** Source for [analytic_set_ideal_unique]: the original
    vanishing membership law is unique, 3.4.5, p. 320. *)
Lemma analytic_set_ideal_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (I J:set (analytic_germ_space hNX a)):
  is_analytic_set_ideal sigma I ->is_analytic_set_ideal sigma J ->I=J.
Proof.
move=>hI hJ;apply/seteqP;split=>alpha.
- by rewrite (analytic_set_ideal_membership hI alpha) (analytic_set_ideal_membership hJ alpha).
- by rewrite (analytic_set_ideal_membership hI alpha) (analytic_set_ideal_membership hJ alpha).
Qed.
