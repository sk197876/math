(** Federer (1969), 3.3.20, p. 308:
    the actual missing-square Omega rule implies a diameter bound. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter FinitePairedMissingPigeonhole
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_paired_missing_metric_diameter]: the
    Omega inference of 3.3.20, p. 308,
    with actual original cells and meeting points.
    The finite counting lemma supplies two hit cells;
    their actual separated points give the diameter
    bound. No original test-set measurability is needed. *)
Theorem finite_paired_missing_metric_diameter (R:realType) (X:metricType R)
    (I:choiceType) (J:finType) (F K:{fset I}) (S:I->set X)
    (T:set X) (e:J*bool->I) (b:R):
  {subset K<=(F `\` finite_cell_hit_indices F S T)%fset} ->
  injective e ->(forall i t,e (i,t) \in F /\e (i,t) \notin K) ->
  (forall i x y,S (e (i,false)) x ->S (e (i,true)) y ->b<=mdist x y) ->
  (#|` ((F `\` finite_cell_hit_indices F S T)%fset)|<#|` K|+#|J|)%N ->
  (b%:E<=extended_metric_diameter T)%E.
Proof.
move=>hK hInjective hEndpoints hDistance hCount.
pose H:=finite_cell_hit_indices F S T.
pose M:=(F `\` H)%fset.
have hMF:{subset M<=F} by move=>i;rewrite in_fsetD=>/andP[].
have [i [hFirst hSecond]]:=@finite_paired_missing_pigeonhole I J F M K e
  hMF hK hInjective hEndpoints hCount.
have hNotAll t:e (i,t) \notin M by case:t;assumption.
have hHit t:e (i,t) \in H.
  have hF: e (i,t) \in F:=(hEndpoints i t).1.
  have hNot:=hNotAll t.
  by move:hNot;rewrite /M in_fsetD hF andbT negbK.
have /finite_cell_hit_indices_membership[_ [x [hxCell hxT]]]:=hHit false.
have /finite_cell_hit_indices_membership[_ [y [hyCell hyT]]]:=hHit true.
apply:le_trans _ (metric_diameter_upper (extended_metric_diameter_specification T) hxT hyT).
by rewrite lee_fin;exact:hDistance i x y hxCell hyCell.
Qed.
