(** Federer (1969), 3.1.1, p. 211: the graph of Df is Borel.
    It is a countable intersection of countable unions of relatively
    closed remainder tests on domain f times Z. The increment tests
    retain the actual domain of f, rather than inspecting arbitrary
    values of a total representative outside that domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassZeroTopology ContinuousOperatorUP ContinuousOperatorNorm
  NormDifferentialRemainderOpen MetricProductBackground TopologicalProductMaps
  TopologicalBorel ContinuousBorelPreimages ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BorelGraph.
Variable R : realType.
Variables X Y Z : lmodType R.
Variable NX : X -> R.
Variable NY : Y -> R.
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable evaluation : Hom Z (Hom X Y).
Variable ZN : Z -> R.
Hypothesis hZ : is_continuous_operator_space NX NY evaluation ZN.
Variable A : set X.
Variable f : X -> Y.
Hypothesis hf : norm_class_zero NX NY A f.
Let E := real_norm_metric_space hNX.
Let T := real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
Let P := metric_product E T.

(** Source for [norm_differential_operator_graph]: the graph of
    Df in X times Z in 3.1.1, p. 211, defined by the exact
    first-order approximation laws at interior domain points. *)
Definition norm_differential_operator_graph : set P :=
  [set p | has_norm_differential NX NY A f p.1 (evaluation p.2)].

(** Source for [norm_remainder_violation]: supporting open
    violation of the i,j remainder test in 3.1.1, p. 211.
    Positive natural reciprocals index error and radius bounds. *)
Definition norm_remainder_violation i j : set P :=
  \bigcup_(h in [set h : X | NX h<(j.+1%:R : R)^-1])
    [set p : P | A p.1 /\ A (p.1+h) /\
      (i.+1%:R : R)^-1*NX h<NY (f (p.1+h)-f p.1-evaluation p.2 h)].

(** Source for [norm_remainder_test]: the relatively closed
    remainder tests C_i,j in 3.1.1, p. 211, with the total
    representative restricted to its actual open domain. *)
Definition norm_remainder_test i j : set P :=
  [set p : P | A p.1] `\` norm_remainder_violation i j.

(** Source for [norm_remainder_violation_open]: arbitrary
    intersections of fixed-increment closed conditions remain
    relatively closed, as used in 3.1.1, p. 211. *)
Lemma norm_remainder_violation_open i j : open (norm_remainder_violation i j).
Proof.
apply: bigcup_open=> h hh.
exact: (@norm_differential_remainder_violation_open R X Y Z NX NY hNX hNY evaluation ZN hZ A f h ((i.+1%:R : R)^-1*NX h) hf).
Qed.

(** Source for [norm_remainder_test_borel]: each C_i,j is
    Borel in X times Z, supporting the graph assertion in
    3.1.1, p. 211. Its relative ambient domain is open. *)
Lemma norm_remainder_test_borel i j : borel_set (norm_remainder_test i j).
Proof.
apply: borel_set_difference.
- exact: (continuous_borel_preimage (@first_projection_continuous E T)
    (open_borel_set (@norm_class_zero_domain_open R X Y NX NY hNX A f hf))).
- exact: (@open_borel_set [the topologicalType of P] (norm_remainder_violation i j) (@norm_remainder_violation_open i j)).
Qed.

(** Source for [norm_differential_graph_countable_formula]:
    the displayed intersection-union graph formula in 3.1.1,
    p. 211. Coinitial positive reciprocals express exactly the
    epsilon remainder, including the zero increment. *)
Theorem norm_differential_graph_countable_formula :
  norm_differential_operator_graph=\bigcap_i \bigcup_j norm_remainder_test i j.
Proof.
apply/seteqP; split=> p.
- move=> hp i _.
  have hi : 0<(i.+1%:R : R)^-1 by rewrite invr_gt0 ltr0n.
  have [d [hd hb]] := norm_differential_remainder hp hi.
  have [j hj] := positive_reciprocal_nat_small hd.
  exists j=> //; split.
  + exact: (@norm_domain_interior_member R X NX hNX A p.1 (norm_differential_interior hp)).
  + move=> [h hh [_ [hah hbad]]].
    have hle := hb h hah (lt_trans hh hj).
    by have := lt_le_trans hbad hle; rewrite ltxx.
- move=> hp.
  have [j0 _ [ha _]] := hp 0%N Logic.I.
  constructor.
  + exact: (@hf p.1 ha).1.
  + exact: continuous_operator_bounded hZ p.2.
  + move=> eps heps.
    have [i hi] := positive_reciprocal_nat_small heps.
    have [j _ [_ hgood]] := hp i Logic.I.
    exists ((j.+1%:R : R)^-1); split; first by rewrite invr_gt0 ltr0n.
    move=> h hah hh.
    have hle : NY (f (p.1+h)-f p.1-evaluation p.2 h)<=(i.+1%:R : R)^-1*NX h.
      rewrite leNgt; apply/negP=> hbad; apply: hgood.
      exists h=> //; by split=> //; split.
    apply: le_trans hle _.
    apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNX.1 h.
    exact: ltW hi.
Qed.

(** Source for [norm_differential_operator_graph_borel]: the
    Borel graph assertion in 3.1.1, p. 211. This part holds
    without finite dimension or completeness; those hypotheses
    are used subsequently to project the graph. *)
Theorem norm_differential_operator_graph_borel : borel_set norm_differential_operator_graph.
Proof.
rewrite norm_differential_graph_countable_formula.
apply: borel_set_countable_intersection; [exact: countableP|by exists 0%N|].
move=> i _; apply: borel_set_countable_union; first exact: countableP.
move=> j _; exact: norm_remainder_test_borel.
Qed.
End BorelGraph.
