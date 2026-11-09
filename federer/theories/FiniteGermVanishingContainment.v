(** Federer (1969), 3.4.5, p. 320: if a
    set germ annihilates all finitely many original equations,
    it is contained in their original zero-system germ.
    Only a finite common neighbourhood is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP
  SetGermUP SetGermOrder FiniteAnalyticVarietyUP FiniteZeroSetSealed
  GermVanishingUP GermVanishingSealed GermVanishingRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_germ_vanishing_containment]: local
    vanishing of a finite equation family gives containment
    in its variety germ, supporting the well-defined var(I)
    in 3.4.5, p. 320. *)
Theorem finite_germ_vanishing_containment (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (I:finType)
    (f:I->@analytic_representative_type R X NX hNX a) (U S:set X):
  U a ->@open (real_norm_metric_space hNX) U ->
  (forall i,@AnalyticSetIdeal.value R X NX hNX a
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S) (analytic_germ (f i))) ->
  set_germ_subset (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S)
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) a
      (@FiniteZeroSet.value [the zmodType of R^o] X U I (fun i=>analytic_representative_value (f i)))).
Proof.
move=>haU hU hVanish.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hex i:=((analytic_set_ideal_representative_equation (f i) S).1 (hVanish i)).
pose V i:=projT1 (cid (hex i)).
have hV i:=projT2 (cid (hex i)).
pose W:set T:=fun x=>forall i,V i x.
have hW:open W.
  rewrite openE=>x hx;apply:(@filter_forall T I _ (nbhs x) (nbhs_filter x))=>i.
  exact:(open_nbhs_nbhs (conj (hV i).1 (hx i))).
apply/set_germ_subset_original;exists (U `&` W);split;first exact:openI hU hW.
split;first by split;[exact:haU|move=>i;exact:(hV i).2.1].
move=>x hx [hu hw].
apply/(original_zero_set_membership (FiniteZeroSet.laws U _) x);split;first exact:hu.
move=>i;exact:(hV i).2.2 x hx (hw i).
Qed.
