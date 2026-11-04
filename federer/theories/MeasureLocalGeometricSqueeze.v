(** Federer (1969), 3.2.46, pp. 281–282: arbitrarily
    small multiplicative distortions on local open patches
    force equality of the full outer measures. This supporting
    lemma expands the book's localization step by countable
    Borel partitions, retaining arbitrary outer test sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP CountableOpenBaseUP TopologicalBorel
  MeasureLocalOpenComparison ExtendedPowerGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_local_geometric_squeeze]: local
    lambda^k comparisons for every lambda>1 identify both
    actual outer measures, supporting 3.2.46, pp. 281–282.
    The Borel partition comparison restricts both measures
    by the original arbitrary target subset first; no
    nonmeasurable hull difference is declared null. *)
Theorem measure_local_geometric_squeeze (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (U : nat -> set X) k :
  is_measure mu -> is_measure nu -> is_countable_open_base U ->
  (forall B, borel_set B -> measure_measurable mu B /\ measure_measurable nu B) ->
  (forall lambda : R, 1<lambda -> forall a, exists V : set X,
    open V /\ V a /\ forall S, S `<=` V ->
      (mu S<=(lambda^+k)%:E*nu S)%E /\ (nu S<=(lambda^+k)%:E*mu S)%E) ->
  mu=nu.
Proof.
move=> hMu hNu hBase hBorel hLocal.
have hGlobal (lambda : R) (hLambda : 1<lambda) S :
    (mu S<=(lambda^+k)%:E*nu S)%E /\ (nu S<=(lambda^+k)%:E*mu S)%E.
  have hPower : 0<=lambda^+k by apply: exprn_ge0; exact: ltW (lt_trans ltr01 hLambda).
  split.
  - apply: (@measure_local_open_comparison R X mu nu U _ hMu hNu hBase hPower hBorel).
    move=> a; have [V [hV [ha hC]]] := hLocal lambda hLambda a.
    exists V; split; first exact hV; split; first exact ha.
    move=> B hB; exact: (hC B hB).1.
  - apply: (@measure_local_open_comparison R X nu mu U _ hNu hMu hBase hPower).
    + move=> B hB; by have [h1 h2] := hBorel B hB; split.
    + move=> a; have [V [hV [ha hC]]] := hLocal lambda hLambda a.
      exists V; split; first exact hV; split; first exact ha.
      move=> B hB; exact: (hC B hB).2.
apply: funext=> S; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@extended_power_geometric_squeeze R (nu S) (mu S) k
    (measure_nonnegative hNu S))=> lambda hLambda.
  exact: (hGlobal lambda hLambda S).1.
- apply: (@extended_power_geometric_squeeze R (mu S) (nu S) k
    (measure_nonnegative hMu S))=> lambda hLambda.
  exact: (hGlobal lambda hLambda S).2.
Qed.
