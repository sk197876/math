(** Federer (1969), 2.10.22, p. 185: replace a finite prefix of
    neighbourhoods by the limiting compact generators while retaining
    arbitrary open neighbourhoods on the remaining positions. The finite
    union is closed, including an empty prefix and inactive positions.
    Source context: CompactGeneratorCostUP.v; the finite-prefix proof form
    is explained in CompactCostOpenResidual.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric MaskedCompactGenerators
  MeasureUP MeasureBasic RegularMeasureUP MetricClosedRemovalBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_mixed_residual_bound]: supporting
    second residual estimate in 2.10.22, p. 185,
    with any finite prefix index set D. The
    target need not be measurable. *)
Theorem compact_cost_mixed_residual_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (B : set X) (v : nat -> bool*compact_hausdorff_space X)
    (D : {fset nat}) (p s : \bar R) :
  is_measure mu -> is_regular_measure mu -> (0<=p)%E ->
  (forall W : nat -> set X, (forall k, open (W k)) ->
    (forall k, masked_compact_set (v k) `<=` W k) ->
    (mu (B `\` \bigcup_k W k)+p<=s)%E) ->
  forall V : nat -> set X, (forall k, k \notin D -> open (V k)) ->
    (forall k, k \notin D -> masked_compact_set (v k) `<=` V k) ->
  (mu (B `\` ((\bigcup_(k in [set` D]) masked_compact_set (v k)) `|`
     \bigcup_(k in ~` [set` D]) V k))+p<=s)%E.
Proof.
move=> hm hr hp hbound V hV hcover.
pose K := \bigcup_(k in [set` D]) masked_compact_set (v k).
pose T := \bigcup_(k in ~` [set` D]) V k.
have hcl k : closed (masked_compact_set (v k)).
  rewrite /masked_compact_set; case: (v k).1; last exact: closed0.
  exact: compact_closed (@metric_hausdorff R X) (set_valP (v k).2).1.
have hK : closed K := @closed_bigcup X [the choiceType of (nat : Type)] [set` D]
  (fun k=>masked_compact_set (v k)) (finite_fset D) (fun k _=>hcl k).
apply: (@regular_measure_closed_removal_bound R X mu B K T p s hm hr hK hp)=> U hU hKU.
pose W k := if k \in D then U else V k.
have hW k : open (W k).
  rewrite /W; case hk: (k \in D)=> //; apply: hV; by rewrite hk.
have hCW k : masked_compact_set (v k) `<=` W k.
  rewrite /W; case hk: (k \in D).
  - move=> x hx; apply: hKU; by exists k.
  - apply: hcover; by rewrite hk.
have hh := hbound W hW hCW.
apply: le_trans _ hh; apply: leeD; last exact: lexx p.
apply: (@measure_mono R X mu hm)=> x [hx hxUT]; split=> //.
move=> [k hk hxk]; rewrite /W in hxk.
case hd: (k \in D) hxk=> hxk; apply: hxUT.
- by left.
- right; exists k=> //; by move=> hkD; change (is_true (k \in D)) in hkD; rewrite hd in hkD.
Qed.
