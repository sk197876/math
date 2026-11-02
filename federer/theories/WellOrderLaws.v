(** General set-theoretic infrastructure for Federer (1969),
    2.1.6, pp. 58-59, which explicitly cites Kelley, Appendix.
    Kelley, General Topology, Appendix, Definition 87 and Theorem 88,
    p. 263 (local Dover 2017 reprint of the 1955 edition), derive
    order laws from the least-element property. We use MathComp's
    proved well-ordering principle as general set-theory background;
    its relation is reflexive, whereas Kelley's is strict. No external
    cardinal-arithmetic or measure theorem is imported. *)
From mathcomp Require Import all_boot boolp classical_sets wochoice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [well_order_reflexive_law]: Kelley Appendix,
    Definition 87/Theorem 88, p. 263; supporting reflexive-convention
    law for Federer's ordinal comparisons in 2.1.6, pp. 58-59.
    The least element of a singleton is that element. *)
Lemma well_order_reflexive_law (T : eqType) (r : rel T) :
  well_order r -> reflexive r.
Proof.
move=> hw x.
have hn : nonempty [pred z | z == x] by exists x; rewrite inE eqxx.
have [z [[hz hl] _]] := hw _ hn.
have he : z = x by move: hz; rewrite inE=> /eqP.
rewrite -he; apply: hl; exact hz.
Qed.

(** Source for [well_order_total_law]: Kelley Appendix,
    Definition 87, p. 263; supporting totality of the reflexive
    relation used for Federer 2.1.6. Compare the least element
    of a two-element set with its other member. *)
Lemma well_order_total_law (T : eqType) (r : rel T) :
  well_order r -> total r.
Proof.
move=> hw x y.
have hn : nonempty [pred z | (z == x) || (z == y)].
  exists x; by rewrite inE eqxx.
have [z [[hz hl] _]] := hw _ hn.
move: hz; rewrite inE=> /orP[/eqP he|/eqP he]; rewrite he in hl.
- apply/orP; left; apply: hl; by rewrite inE eqxx orbT.
- apply/orP; right; apply: hl; by rewrite inE eqxx.
Qed.

(** Source for [well_order_antisymmetric_law]: Kelley Appendix,
    Theorem 88, p. 263; supporting reflexive counterpart of strict
    asymmetry for Federer 2.1.6. Two mutually preceding elements
    are both least in their pair, so uniqueness identifies them. *)
Lemma well_order_antisymmetric_law (T : eqType) (r : rel T) :
  well_order r -> antisymmetric r.
Proof.
move=> hw x y /andP[hxy hyx].
have hr := well_order_reflexive_law hw.
have hn : nonempty [pred z | (z == x) || (z == y)].
  exists x; by rewrite inE eqxx.
have [z [_ hu]] := hw _ hn.
have hx : minimum_of r [pred z | (z == x) || (z == y)] x.
  split; first by rewrite inE eqxx.
  move=> t; rewrite inE=> /orP[/eqP->|/eqP->] //; exact: hr.
have hy : minimum_of r [pred z | (z == x) || (z == y)] y.
  split; first by rewrite inE eqxx orbT.
  move=> t; rewrite inE=> /orP[/eqP->|/eqP->] //; exact: hr.
by rewrite -(hu x hx) (hu y hy).
Qed.

(** Source for [well_order_transitive_law]: Kelley Appendix,
    Theorem 88, p. 263; supporting order-transitivity proof for
    Federer 2.1.6. Taking the least element of a three-element set
    excludes the only possible failure of transitivity. *)
Lemma well_order_transitive_law (T : eqType) (r : rel T) :
  well_order r -> transitive r.
Proof.
move=> hw y x z hxy hyz.
have ha := well_order_antisymmetric_law hw.
have hn : nonempty [pred t | [|| t == x, t == y | t == z]].
  exists x; by rewrite inE eqxx.
have [t [[ht hl] _]] := hw _ hn.
have htx : r t x by apply: hl; rewrite inE eqxx.
have hty : r t y by apply: hl; rewrite inE eqxx orbT.
have htz : r t z by apply: hl; rewrite inE eqxx !orbT.
move: ht; rewrite inE=> /or3P[/eqP he|/eqP he|/eqP he].
- by rewrite -he.
- have hexy : x = y by apply: ha; apply/andP; split=> //; rewrite -he.
  by rewrite hexy.
- have heyz : y = z by apply: ha; apply/andP; split=> //; rewrite -he.
  by rewrite -heyz.
Qed.

(** Source for [well_order_set_minimum]: Kelley Appendix,
    Definition 87, p. 263; supporting least-element adapter for
    nonempty predicate sets in Federer 2.1.6, pp. 58-59. *)
Lemma well_order_set_minimum (T : eqType) (r : rel T) (A : set T) :
  well_order r -> (exists x, A x) ->
  exists x, A x /\ forall y, A y -> r x y.
Proof.
move=> hw [a ha].
have hn : nonempty [pred x | x \in A].
  exists a; exact: mem_set ha.
have [x [[hx hl] _]] := hw _ hn.
exists x; split; first exact: set_mem hx.
move=> y hy; apply: hl; exact: mem_set hy.
Qed.
