(** Federer (1969), 3.2.46, p. 282: local
    coordinate null-fibre conclusions assemble over a
    countable open cover. This supporting measure argument
    uses 2.1.3, pp. 55–56, and 2.3.1,
    p. 72; no coarea identity is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof MappingMultiplicity
  MeasureUP MeasureBasic MeasureIndexedCover MeasureAlmostUP MeasureAlmostBasic
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_local_fibre_null_transfer]:
    a common conull target region controls every original
    null source fibre once local coordinate null-fibre
    theorems are proved, supporting 3.2.46, p. 282.
    Arbitrary nonmeasurable source subsets and infinite
    ambient measures are retained; only a countable open
    base and the three actual measure laws are required. *)
Theorem measure_local_fibre_null_transfer (R : realType) (X : topologicalType)
    (Y : choiceType) (mu sigma : set X -> \bar R) (beta : set Y -> \bar R)
    (f : X -> Y) (U : nat -> set X) :
  is_measure mu -> is_measure sigma -> is_measure beta -> is_countable_open_base U ->
  (forall x, exists V : set X, open V /\ V x /\ forall N, N `<=` V -> mu N=0 ->
    measure_almost_everywhere beta [set y | sigma (mapping_fibre f N y)=0]) ->
  forall N, mu N=0 ->
    measure_almost_everywhere beta [set y | sigma (mapping_fibre f N y)=0].
Proof.
move=> hMu hSigma hBeta hBase hLocal N hNull.
pose C := [set V : set X | open V /\ forall P, P `<=` V -> mu P=0 ->
  measure_almost_everywhere beta [set y | sigma (mapping_fibre f P y)=0]].
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx hTransfer]]] := hLocal x.
  exists V; last exact hx; by split.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
have hPiece V (hVG : G V) :
    measure_almost_everywhere beta [set y | sigma (mapping_fibre f (N `&` V) y)=0].
  apply:(hGC V hVG).2.
  - by move=> x [_ hx].
  - apply:(measure_null_subset hMu _ hNull); by move=> x [hx _].
have hAll := @measure_almost_everywhere_countable R Y [the choiceType of set X]
  beta hBeta G (fun V=>[set y | sigma (mapping_fibre f (N `&` V) y)=0]) hCount hPiece.
apply:(@measure_almost_everywhere_mono R Y beta hBeta _ _ _ hAll)=> y hy.
have hFibreCover : mapping_fibre f N y `<=`
    \bigcup_(V in G) mapping_fibre f (N `&` V) y.
  move=> x [hx hxy]; have [V hVG hxV] := hGCover x Logic.I.
  exists V; first exact hVG; split; last exact hxy; by split.
have hBound := @measure_indexed_cover R X [the choiceType of set X] sigma hSigma
  (mapping_fibre f N y) G (fun V=>mapping_fibre f (N `&` V) y) hCount hFibreCover.
rewrite (nonnegative_sum_zero (fun V hVG=>hy V hVG)) in hBound.
by apply/eqP; rewrite eq_le hBound (measure_nonnegative hSigma).
Qed.
