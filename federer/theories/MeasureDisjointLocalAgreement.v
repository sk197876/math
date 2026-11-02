(** Federer (1969), 3.2.23, p. 260: countably many injective
    image pieces and the null remainder identify the whole measure.
    This supporting argument restricts both measures by an arbitrary
    test set before countable additivity; test sets need not be Borel. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal.
From Federer Require Import MeasureUP MeasureRestriction MeasureAlmostBasic
  MeasureAlmostDisjointSum NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_disjoint_local_agreement]: supporting
    countable gluing in the last sentence of Federer 3.2.23,
    p. 260, from the countable splitting law of 2.1.3, p. 55.
    Equality of the full restrictions on disjoint measurable pieces,
    together with two null omitted sets, implies equality on every
    subset. Neither finite total mass nor global regularity is required. *)
Theorem measure_disjoint_local_agreement (R:realType) (X I:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu) (hn:is_measure nu)
    (D:set I) (P:I->set X):
  countable D ->
  (forall i,D i ->measure_measurable mu (P i) /\measure_measurable nu (P i)) ->
  (forall i j,D i ->D j ->i!=j ->forall x,P i x ->P j x ->False) ->
  mu (~` (\bigcup_(i in D) P i))=0 ->nu (~` (\bigcup_(i in D) P i))=0 ->
  (forall i,D i ->measure_restrict mu (P i)=measure_restrict nu (P i)) ->mu=nu.
Proof.
move=>hCount hMeas hDisjoint hNullM hNullN hLocal.
apply:funext=>S.
pose mS:=measure_restrict mu S.
pose nS:=measure_restrict nu S.
have hmS:=measure_restrict_is_measure hm S.
have hnS:=measure_restrict_is_measure hn S.
have hNullMS:mS (setT `\` (\bigcup_(i in D) P i))=0.
  apply:(measure_null_subset hm _ hNullM); by move=>x [_ [_ hx]].
have hNullNS:nS (setT `\` (\bigcup_(i in D) P i))=0.
  apply:(measure_null_subset hn _ hNullN); by move=>x [_ [_ hx]].
have hSumM:=@measure_almost_disjoint_cover_sum R X I mS hmS setT D P hCount
  (fun _ _ _ _=>Logic.I) hDisjoint (fun i hi=>@measure_restrict_measurable R X mu S (P i) (hMeas i hi).1) hNullMS.
have hSumN:=@measure_almost_disjoint_cover_sum R X I nS hnS setT D P hCount
  (fun _ _ _ _=>Logic.I) hDisjoint (fun i hi=>@measure_restrict_measurable R X nu S (P i) (hMeas i hi).2) hNullNS.
change (mu S=nu S).
have hValues i (hi:D i):mS (P i)=nS (P i).
  have h:=congr1 (fun rho=>rho S) (hLocal i hi).
  by rewrite /mS /nS /measure_restrict (setIC S (P i)).
have hTotalM:mS setT=mu S by rewrite /mS /measure_restrict setIT.
have hTotalN:nS setT=nu S by rewrite /nS /measure_restrict setIT.
rewrite hTotalM in hSumM.
rewrite hTotalN in hSumN.
rewrite hSumM hSumN; apply:nonnegative_sum_ext=>i hi.
exact:hValues i hi.
Qed.
