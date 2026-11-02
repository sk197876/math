(** Federer (1969), 3.1.1, p. 211: project a Borel graph
    injectively onto its domain, using 2.2.10, p. 67. The
    same argument applied to the part over a Borel target set
    proves Borel measurability of the represented function. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP MetricProductBackground MetricProductCompleteness
  MetricProductSeparability TopologicalProductMaps TopologicalBorel BorelFamilyBasic
  ContinuousBorelPreimages InjectiveBorelImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_single_valued_graph_preimage]: the Borel
    projection argument of 3.1.1, p. 211, stated for an arbitrary
    single-valued Borel graph in two complete separable metric
    spaces. Every Borel target inverse image is Borel. *)
Theorem borel_single_valued_graph_preimage (R : realType) (X Y : metricType R)
    (G : set (metric_product X Y)) :
  is_complete_metric_space X -> is_complete_metric_space Y ->
  (exists D : set X, countable D /\ dense D) ->
  (exists D : set Y, countable D /\ dense D) ->
  borel_set G -> (forall x y z, G (x,y) -> G (x,z) -> y=z) ->
  forall B : set Y, borel_set B -> borel_set [set x : X | exists y, G (x,y) /\ B y].
Proof.
move=> hX hY hsX hsY hG huniq B hB.
pose P := [the metricType R of metric_product X Y].
pose H : set P := G `&` (@snd X Y @^-1` B).
have hH : borel_set H.
  apply: (borel_family_binary_intersection (borel_sets_family P) hG).
  exact: (continuous_borel_preimage (@second_projection_continuous X Y) hB).
have hinj : forall p q : P, H p -> H q -> p.1=q.1 -> p=q.
  move=> [x y] [x' z] [hp _] [hq _] /= he; subst x'.
  by have -> := huniq x y z hp hq.
have hb := @injective_borel_image_borel R P X (@fst X Y) H
  (complete_metric_product hX hY) (separable_metric_product hsX hsY)
  (@metric_hausdorff R X) (@first_projection_continuous X Y) hH hinj.
have he : [set x : X | exists y, G (x,y) /\ B y]=(@fst X Y @` H).
  apply/seteqP; split=> x.
  - move=> [y hy]; by exists (x,y).
  - move=> [[a y] [hG' hB'] /= <-]; by exists y.
by rewrite he.
Qed.
