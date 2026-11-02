(** Federer (1969), 2.2.10(2), p. 67: one step of the B(s) construction.
    Separate the disjoint Suslin images of the source partition pieces, then
    intersect the Borel containers with their parent and the prescribed
    closed image bound. Source context and conventions: BorelImageTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP ClosedCoverTreeUP CoverPartitionTreeUP
  CoverPartitionTreeBasic BorelFamilyBasic TopologicalBorel BorelClosedProjection
  SuslinSetUP SuslinImageContainers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [injective_partition_child_images_disjoint]: supporting
    disjointness assertion in Federer 2.2.10(2), p. 67. Injectivity on C
    transfers disjointness of the partition pieces A(s,j) to their images
    after intersecting C. *)
Lemma injective_partition_child_images_disjoint (X : Type) (Y : Type)
    (f : X -> Y) (C : set X) (E A : seq nat -> set X)
    (hA : is_cover_partition_tree E A) s :
  (forall x y, C x -> C y -> f x = f y -> x = y) ->
  forall i j, i <> j ->
    (f @` (C `&` A (i::s))) `&` (f @` (C `&` A (j::s))) = set0.
Proof.
move=> hf i j hij; apply/seteqP; split; last by move=> y [].
move=> y [[x [hx hxi] hfx] [z [hz hzj] hfz]].
have he : x = z by apply: hf hx hz _; rewrite hfx hfz.
have hh : (A (i::s) `&` A (j::s)) x by split=> //; rewrite he.
by rewrite (@cover_partition_children_disjoint X E A hA s i j hij) in hh.
Qed.

(** Source for [borel_image_child_refinement]: supporting Borel child choice
    in Federer 2.2.10(2), p. 67. The parent already contains f(C intersect
    A(s)); the chosen children retain containment, disjointness, nesting and
    the closure bound. *)
Lemma borel_image_child_refinement (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C : set T)
    (E A : seq nat -> set T) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) (V : set Y) s :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) -> hausdorff_space Y -> continuous f ->
  closed C -> (forall x y, C x -> C y -> f x = f y -> x = y) ->
  borel_set V -> (f @` (C `&` A s)) `<=` V ->
  exists B : nat -> set Y,
    (forall j, borel_set (B j) /\ (f @` (C `&` A (j::s))) `<=` B j /\
      B j `<=` V /\ B j `<=` closure (f @` (C `&` E (j::s)))) /\
    forall i j, i <> j -> B i `&` B j = set0.
Proof.
move=> hT hsep hY hf hC hinj hV hparent.
have hS j : is_suslin_set R (C `&` A (j::s)).
  apply: metric_borel_suslin.
  apply: (@borel_family_binary_intersection T setT _ (borel_sets_family T)).
  - exact: closed_borel_set hC.
  - exact: (@cover_partition_borel R T E A hE hA (j::s)).
have hdis := @injective_partition_child_images_disjoint T Y f C E A hA s hinj.
have [D [hD hd]] := @disjoint_suslin_images_borel_containers R T Y f
  (fun j => C `&` A (j::s)) hT hsep hY hf hS hdis.
pose B j := D j `&` (V `&` closure (f @` (C `&` E (j::s)))).
exists B; split.
- move=> j; split.
  + apply: (@borel_family_binary_intersection Y setT _ (borel_sets_family Y)); first exact: (hD j).1.
    apply: (@borel_family_binary_intersection Y setT _ (borel_sets_family Y))=> //.
    exact: (@closed_borel_set Y (closure (f @` (C `&` E (j::s))))
      (@closed_closure Y (f @` (C `&` E (j::s))))).
  + split.
    * move=> y hy; split; first exact: (hD j).2 y hy.
      have [x [hx hax] hfx] := hy; split.
      -- apply: hparent; exists x=> //; split=> //; exact: (@cover_partition_child_subset T E A hA s j x hax).
      -- apply: subset_closure; exists x=> //; split=> //.
         exact: (@cover_partition_within_cover R T E A hE hA (j::s) x hax).
    * split; [by move=> y [_ [hy _]]|by move=> y [_ [_ hy]]].
- move=> i j hij; apply/seteqP; split; last by move=> y [].
  move=> y [[hi _] [hj _]]; have hh : (D i `&` D j) y by split.
  by rewrite (hd i j hij) in hh.
Qed.
