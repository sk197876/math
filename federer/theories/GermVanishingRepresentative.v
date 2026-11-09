(** Federer (1969), 3.4.5, p. 320: the
    sealed ideal membership law is equivalent to vanishing
    for any one pair of original representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LocalGermUP LocalGermSealed
  AnalyticGermRepresentatives AnalyticGermUP SetGermUP GermVanishingUP GermVanishingLaws GermVanishingSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_set_ideal_representative_equation]:
    the displayed original vanishing condition and dependence
    only on gamma_a(S), 3.4.5, p. 320.
    No representative choice appears in the public ideal. *)
Theorem analytic_set_ideal_representative_equation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (f:@analytic_representative_type R X NX hNX a)
    (S:set (Topological.clone (real_norm_metric_space hNX) _)):
  @AnalyticSetIdeal.value R X NX hNX a
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S) (analytic_germ f) <->
  @vanishes_near_on (Topological.clone (real_norm_metric_space hNX) _) [the zmodType of R^o]
    a S (analytic_representative_value f).
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
have hLaw:=@AnalyticSetIdeal.laws R X NX hNX a (@set_germ T a S).
rewrite (analytic_set_ideal_membership hLaw (analytic_germ f));split.
- move=>h;exact:(h f S (erefl _) (erefl _)).
- move=>hVan g V hGerm hSet.
  have hSets:@locally_equal_at T Prop a S V.
    apply/(local_germ_equality (@LocalGerms.laws T Prop [the choiceType of set T] (fun S=>S) a)).
    exact:esym hSet.
  have hFunctions:@locally_equal_at T R a (value f) (value g).
    apply/(local_germ_equality (@LocalGerms.laws T R P value a)).
    exact:esym hGerm.
  exact:(@vanishes_near_representative_independence T [the comNzRingType of (R:Type)]
    a S V (value f) (value g) hSets hFunctions hVan).
Qed.
