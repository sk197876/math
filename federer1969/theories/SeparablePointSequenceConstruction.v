(** Federer (1969), 2.4.12, p. 87: private dense sequence witness for
    finite-image approximation. Source context and role:
    SeparablePointSequenceUP.v. This existence construction reuses the
    previously proved private enumeration of nonempty countable sets;
    downstream proofs see only the sealed dense-sequence laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import SeparableClosedCover SeparablePointSequenceUP CountableBorelApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [based_dense_sequence_exists]: supporting existence of a
    dense sequence starting at a prescribed point in Federer 2.4.12, p. 87
    Adding the prescribed first value preserves density and permits finite
    separable spaces as well as infinite ones. *)
Theorem based_dense_sequence_exists (R : realType) (Y : metricType R)
    (y0 : Y) (D : set Y) : countable D -> dense D -> exists y, is_based_dense_sequence y0 y.
Proof.
move=> hc hd.
have hDn : D !=set0.
  have [z [hz _]] := metric_dense_point_near hd y0 (@ltr01 R); by exists z.
have [u hu] := countable_nonempty_point_enumeration hc hDn.
pose y n := if n is k.+1 then u k else y0.
exists y; split=> //.
move=> U hn ho; have [z [hzU hz]] := hd U hn ho.
exists z; split=> //; rewrite -hu in hz; have [k _ hk] := hz.
exists k.+1=> //; exact hk.
Qed.
