(** Federer (1969), 3.2.38, p. 275: the two finite
    good and bad cube families cover the actual original image. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MinkowskiContents FiniteMinkowskiTubeCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_two_minkowski_image_tube_cover]: the first
    inequality in the final display of Federer 3.2.38, p. 275.
    The disjoint sum of the two finite index types applies the
    actual finite tube cover, even if either family is empty. *)
Lemma finite_two_minkowski_image_tube_cover (R:realType) (X:Type) n m (G B:finType)
    (f:X->inner_metric_space (@euclidean_inner_productP R n))
    (C:set X) (QG:G->set X) (QB:B->set X) (r:R):
  (0<r)%R ->C `<=` (\bigcup_i QG i) `|` (\bigcup_i QB i) ->
  minkowski_tube_quotient m (f @` C) r<=
    (\sum_i minkowski_tube_quotient m (f @` QG i) r)+
    (\sum_i minkowski_tube_quotient m (f @` QB i) r).
Proof.
move=>hr hCover.
pose I:=[the finType of (G+B)%type].
pose Q (i:I):=match i with inl g=>QG g|inr b=>QB b end.
have hAll:C `<=` \bigcup_i Q i.
  move=>x hx; have [[i _ hi]|[i _ hi]]:=hCover x hx.
  - by exists (inl i:I).
  - by exists (inr i:I).
have h:=@finite_minkowski_image_tube_cover R X n m I f C Q r hr hAll.
by rewrite big_sumType /= in h.
Qed.
