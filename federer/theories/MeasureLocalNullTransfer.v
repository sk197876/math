(** Federer (1969), 3.2.46, pp. 281–282: null-set
    comparisons may be localised in a space with a countable
    open base. This supports the critical-image and null-fibre
    reductions for the Riemannian area/coarea extensions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof
  MeasureUP MeasureAlmostBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_local_null_transfer]: a local
    null-set implication on every actual open neighbourhood
    gives the global implication, supporting 3.2.46,
    pp. 281–282. Neither source nor exceptional subset
    is assumed measurable, finite or nonempty. *)
Lemma measure_local_null_transfer (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (U : nat -> set X) :
  is_measure mu -> is_measure nu -> is_countable_open_base U ->
  (forall x, exists V : set X, open V /\ V x /\
    forall S, S `<=` V -> nu S=0 -> mu S=0) ->
  forall S, nu S=0 -> mu S=0.
Proof.
move=> hMu hNu hBase hLocal S hNull.
pose C := [set V : set X | open V /\ forall B, B `<=` V -> nu B=0 -> mu B=0].
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx hBound]]] := hLocal x.
  exists V; last exact hx; by split.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
have hPiece V (hV : G V) : mu (S `&` V)=0.
  apply: (hGC V hV).2; first by move=> x [_ hx].
  apply: (measure_null_subset hNu _ hNull); by move=> x [hx _].
have hS : S `<=` \bigcup_(V in G) (S `&` V).
  move=> x hx; have [V hV hxV] := hGCover x Logic.I.
  exists V; first exact hV; by split.
have hBound := measure_indexed_cover hMu hCount hS.
rewrite (nonnegative_sum_zero hPiece) in hBound.
by apply/eqP; rewrite eq_le hBound (measure_nonnegative hMu).
Qed.
