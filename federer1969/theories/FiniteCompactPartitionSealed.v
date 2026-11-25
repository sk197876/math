(** Opaque finite partition of unity for Federer (1969), 2.5.14, p. 108.
    Specifications and Source context are in FiniteCompactPartitionUP.v. The
    finite induction used for existence is hidden from the integral
    arguments. *)
From mathcomp Require Import all_boot finmap boolp classical_sets reals topology.
From Federer Require Import FiniteCompactPartitionUP FiniteCompactPartitionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type FiniteCompactPartitionSignature.
(** Source for [value]: the finite family g_n from Federer
    2.5.14, p. 108. *)
Parameter value : forall (R : realType) (X : topologicalType) (J : choiceType)
  (V : J -> set X) (F : {fset J}) (K : set X), hausdorff_space X -> locally_compact (@setT X) ->
  compact K -> (forall j, j \in F -> open (V j)) ->
  K `<=` \bigcup_(j in [set` F]) V j -> J -> X -> R.
(** Source for [laws]: the support, range and sum laws for g_n
    in Federer 2.5.14, p. 108. *)
Parameter laws : forall (R : realType) (X : topologicalType) (J : choiceType)
  (V : J -> set X) (F : {fset J}) (K : set X)
  (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K)
  (hV : forall j, j \in F -> open (V j)) (hc : K `<=` \bigcup_(j in [set` F]) V j),
  is_finite_compact_partition V F K (@value R X J V F K hh hl hK hV hc).
End FiniteCompactPartitionSignature.
Module FiniteCompactPartition : FiniteCompactPartitionSignature.
(** Source for [value]: private choice of the proved partition
    witness for Federer 2.5.14, p. 108. *)
Definition value (R : realType) (X : topologicalType) (J : choiceType)
  (V : J -> set X) (F : {fset J}) (K : set X)
  (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K)
  (hV : forall j, j \in F -> open (V j)) (hc : K `<=` \bigcup_(j in [set` F]) V j) :=
  projT1 (cid (@finite_compact_partition_exists R X J V hh hl F K hK hV hc)).
(** Source for [laws]: the chosen witness satisfies the partition
    specification of Federer 2.5.14, p. 108. *)
Lemma laws (R : realType) (X : topologicalType) (J : choiceType)
  (V : J -> set X) (F : {fset J}) (K : set X)
  (hh : hausdorff_space X) (hl : locally_compact (@setT X)) (hK : compact K)
  (hV : forall j, j \in F -> open (V j)) (hc : K `<=` \bigcup_(j in [set` F]) V j) :
  is_finite_compact_partition V F K (@value R X J V F K hh hl hK hV hc).
Proof. exact: projT2 (cid (@finite_compact_partition_exists R X J V hh hl F K hK hV hc)). Qed.
End FiniteCompactPartition.
