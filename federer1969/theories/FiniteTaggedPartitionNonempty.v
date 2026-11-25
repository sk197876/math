(** Federer (1969), 4.1.23, p. 380:
    remove empty members of the original
    finite tagged Borel partition before using
    its tags as points of B.
    The source B itself may be empty;
    then the resulting finite type is empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import FiniteTaggedBorelPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_tagged_partition_remove_empty]:
    the actual b_k in B_k used
    for Q in Federer 4.1.23,
    p. 380. Removing empty cells
    preserves every partition and mesh law
    and introduces no arbitrary point of B. *)
Theorem finite_tagged_partition_remove_empty (R : realType)
    (X : metricType R) (K : set X) e
    (I : finType) (A : I -> set X) (tag : I -> X)
    (hP : is_finite_tagged_borel_partition K e A tag) :
  exists (J : finType) (B : J -> set X) (b : J -> X),
    is_finite_tagged_borel_partition K e B b /\
    forall j, B j (b j).
Proof.
pose J : finType := [the finType of {i : I | `[< A i !=set0 >]}].
pose B := fun j : J => A (val j).
pose b := fun j : J => tag (val j).
have hNonempty (j : J) : A (val j) !=set0.
  exact: (elimT (asboolP _) (valP j)).
exists J,B,b; split.
- constructor.
  + move=> j; exact: (finite_tagged_partition_borel hP (val j)).
  + move=> j x hx.
    exact: (@finite_tagged_partition_inside R X K e I A tag hP (val j) x hx).
  + move=> x hx.
    have [i hi] := @finite_tagged_partition_cover R X K e I A tag hP x hx.
    have hCellNonempty : A i !=set0 by exists x.
    exists (Sub i (introT (asboolP _) hCellNonempty)); exact: hi.
  + move=> i j x hx hy; apply: val_inj.
    exact: (@finite_tagged_partition_disjoint R X K e I A tag hP
      (val i) (val j) x hx hy).
  + move=> j _.
    exact: (@finite_tagged_partition_tag R X K e I A tag hP (val j) (hNonempty j)).
  + move=> j x hx.
    exact: (@finite_tagged_partition_mesh R X K e I A tag hP (val j) x hx).
- move=> j.
  exact: (@finite_tagged_partition_tag R X K e I A tag hP (val j) (hNonempty j)).
Qed.
