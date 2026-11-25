(** General topology in Federer (1969), 2.2.12, p. 69: separate the compact
    fiber {a} times K from the closed witness Z by a product V times W, with
    a in V and K contained in W. We derive the tube from product
    neighborhoods and a finite subcover. No Hausdorff condition on X is
    needed. its sequence-product background is 2.29–2.31, pp. 16–17. Source
    editions: SequenceBoxes.v. *)
From mathcomp Require Import all_boot finmap boolp classical_sets topology.
From Federer Require Import CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_open_intersection]: supporting general
    topology for the tube in Federer 2.2.12, p. 69.
    A finite intersection of open sets is open; the empty
    intersection is the whole space. *)
Lemma finite_open_intersection (T : topologicalType) (J : choiceType)
    (D : {fset J}) (F : J -> set T) :
  (forall i, i \in D -> open (F i)) -> open (\bigcap_(i in [set` D]) F i).
Proof.
move=> ho; rewrite openE=> x hx.
apply: filter_bigI=> i hi; have h := ho i hi; rewrite openE in h; exact: h x (hx i hi).
Qed.

(** Source for [open_product_rectangle_at]: supporting rectangle
    refinement for Federer 2.2.12, p. 69. Every open
    neighborhood of a product point contains a product of open
    neighborhoods of the two coordinates. *)
Lemma open_product_rectangle_at (X Y : topologicalType) (O : set (X * Y)) x y :
  open O -> O (x,y) -> exists V W, open V /\ open W /\ V x /\ W y /\ V `*` W `<=` O.
Proof.
move=> ho hxy; have hn : nbhs (x,y) O by rewrite openE in ho; exact: ho _ hxy.
have [[A B] [hA hB] hAB] := hn.
rewrite nbhsE in hA.
rewrite nbhsE in hB.
have [V [hV hx] hVA] := hA; have [W [hW hy] hWB] := hB.
exists V, W; split=> //; split=> //; split=> //; split=> //.
move=> [u v] [hu hv]; apply: hAB; split; [exact: hVA u hu|exact: hWB v hv].
Qed.

(** Source for [compact_fiber_closed_tube]: direct product
    separation step in Federer 2.2.12, p. 69. If a
    closed subset misses the compact fiber at a, finitely many
    product neighborhoods provide open V,W with a in V, K in W,
    and V times W disjoint from the closed set. *)
Theorem compact_fiber_closed_tube (X Y : topologicalType) (Z : set (X * Y))
    (K : set Y) (a : X) : closed Z -> compact K ->
  (forall y, K y -> ~ Z (a,y)) ->
  exists V W, open V /\ open W /\ V a /\ K `<=` W /\
    forall x y, V x -> W y -> ~ Z (x,y).
Proof.
move=> hZ hK hdis.
pose D : set (set X * set Y) := [set p |
  open p.1 /\ open p.2 /\ p.1 a /\ p.1 `*` p.2 `<=` ~` Z].
have hcover : K `<=` \bigcup_(p in D) p.2.
  move=> y hy.
  have [V [W [hV [hW [ha [hyW hrect]]]]]] :=
    open_product_rectangle_at (closed_openC hZ) (hdis y hy).
  exists (V,W); last exact hyW.
  split=> //; split=> //; by split.
have hopen p : D p -> open p.2 by move=> [_ []].
have [F hF hcov] := compact_open_finite_cover hK hopen hcover.
have hFD p : p \in F -> D p by move=> hp; exact: set_mem (hF p hp).
pose V := \bigcap_(p in [set` F]) p.1.
pose W := \bigcup_(p in [set` F]) p.2.
exists V, W; split.
- apply: finite_open_intersection=> p hp; exact: (hFD p hp).1.
- split.
  + apply: bigcup_open=> p hp; exact: (hFD p hp).2.1.
  + split.
    * move=> p hp; exact: (hFD p hp).2.2.1.
    * split; first exact hcov.
      move=> x y hx [p hp hy]; apply: (hFD p hp).2.2.2.
      by split; first exact: hx p hp.
Qed.
