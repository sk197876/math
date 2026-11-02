(** Federer (1969), 2.2.10(2), p. 67: sealed Borel image tree B(s). The
    signature exposes only the sets and their abstract laws; recursive
    container choices remain private. Source context: BorelImageTreeUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP ClosedCoverTreeUP CoverPartitionTreeUP
  BorelImageTreeUP BorelImageTreeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type BorelImageTreeSignature.
(** Source for [value]: abstract B(s) witnesses in the injective
    closed-image proof of Federer 2.2.10(2), p. 67. *)
Parameter value : forall (R : realType) (T : metricType R) (Y : topologicalType) (f : T -> Y)
    (C : set T) (E A : seq nat -> set T)
    (hE : is_closed_cover_tree E) (hA : is_cover_partition_tree E A)
    (hT : is_complete_metric_space T)
    (hsep : exists H : set T, countable H /\ dense H)
    (hY : hausdorff_space Y) (hf : continuous f) (hC : closed C)
    (hinj : forall x y, C x -> C y -> f x = f y -> x = y), seq nat -> set Y.
(** Source for [laws]: the Borel, image-containment, nesting and
    closure properties of B(s) in Federer 2.2.10(2), p. 67. *)
Parameter laws : forall (R : realType) (T : metricType R) (Y : topologicalType) (f : T -> Y)
    (C : set T) (E A : seq nat -> set T)
    (hE : is_closed_cover_tree E) (hA : is_cover_partition_tree E A)
    (hT : is_complete_metric_space T)
    (hsep : exists H : set T, countable H /\ dense H)
    (hY : hausdorff_space Y) (hf : continuous f) (hC : closed C)
    (hinj : forall x y, C x -> C y -> f x = f y -> x = y),
  is_borel_image_tree f C E A (@value R T Y f C E A hE hA hT hsep hY hf hC hinj).
End BorelImageTreeSignature.
Module BorelImageTree : BorelImageTreeSignature.
(** Source for [value]: private witness selection from the proved
    tree existence for Federer 2.2.10(2), p. 67. *)
Definition value (R : realType) (T : metricType R) (Y : topologicalType) (f : T -> Y)
    (C : set T) (E A : seq nat -> set T)
    (hE : is_closed_cover_tree E) (hA : is_cover_partition_tree E A)
    (hT : is_complete_metric_space T)
    (hsep : exists H : set T, countable H /\ dense H)
    (hY : hausdorff_space Y) (hf : continuous f) (hC : closed C)
    (hinj : forall x y, C x -> C y -> f x = f y -> x = y) :=
  projT1 (cid (@borel_image_tree_exists R T Y f C E A hE hA hT hsep hY hf hC hinj)).
(** Source for [laws]: the selected tree satisfies all abstract
    B(s) laws for Federer 2.2.10(2), p. 67. *)
Lemma laws (R : realType) (T : metricType R) (Y : topologicalType) (f : T -> Y)
    (C : set T) (E A : seq nat -> set T)
    (hE : is_closed_cover_tree E) (hA : is_cover_partition_tree E A)
    (hT : is_complete_metric_space T)
    (hsep : exists H : set T, countable H /\ dense H)
    (hY : hausdorff_space Y) (hf : continuous f) (hC : closed C)
    (hinj : forall x y, C x -> C y -> f x = f y -> x = y) :
  is_borel_image_tree f C E A (@value R T Y f C E A hE hA hT hsep hY hf hC hinj).
Proof. exact: projT2 (cid (@borel_image_tree_exists R T Y f C E A hE hA hT hsep hY hf hC hinj)). Qed.
End BorelImageTree.
