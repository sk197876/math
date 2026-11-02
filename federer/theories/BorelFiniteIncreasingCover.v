(** Federer (1969), 2.10.24(1), p. 187: supporting Borel exhaustion of a
    countable union of finite-measure sets, using Borel regularity 2.2.3,
    pp. 61–62. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_finite_increasing_cover]: supporting
    preliminary exhaustion for the B_j construction of
    2.10.24(1), p. 187. The initial sets may
    be nonmeasurable. Their Borel hulls have equal
    finite measure; finite initial unions are increasing. *)
Theorem borel_finite_increasing_cover (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (A : nat -> set X) :
  is_measure mu -> is_borel_regular_measure mu -> (forall n, mu (A n)< +oo) ->
  exists B : nat -> set X,
    (forall n, borel_set (B n)) /\ (forall n, mu (B n)< +oo) /\
    (forall n m, (n<=m)%N -> B n `<=` B m) /\
    (\bigcup_n A n) `<=` \bigcup_n B n.
Proof.
move=> hm hr hAfin.
pose C n := projT1 (cid (borel_regular_cover hr (A n))).
have hC n := projT2 (cid (borel_regular_cover hr (A n))).
pose B n := \bigcup_(i in [set i | (i<n)%N]) C i.
have hB n : borel_set (B n).
  apply: (@borel_set_countable_union X [the choiceType of (nat : Type)] [set i | (i<n)%N] C (countableP _))=> i hi; exact: (hC i).2.1.
have hB0 : B 0%N=set0 by apply/seteqP; split=> x // [i hi _]; move: hi; rewrite /= ltn0.
have hBS n : B n.+1=B n `|` C n.
  apply/seteqP; split=> x.
  - move=> [i hi hx]; move: hi; rewrite /= ltnS leq_eqVlt=> /orP[/eqP he|hi].
    + right; by rewrite -he.
    + left; by exists i.
  - move=> [[i hi hx]|hx]; [exists i=> //; exact: ltn_trans hi (ltnSn n)|exists n=> //; exact: ltnSn].
have hfinite n : mu (B n)< +oo.
  elim: n=> [|n ih]; first by rewrite hB0 (measure_empty hm); exact: ltry.
  rewrite hBS; apply: le_lt_trans (@measure_binary_cover R X mu hm _ _ _ (fun x hx=>hx)) _.
  apply: lte_add_pinfty ih _; by rewrite -(hC n).2.2.
exists B; split=> //; split=> //; split.
- move=> n m hnm x [i hi hx]; exists i=> //; exact: leq_trans hi hnm.
- move=> x [n _ hx]; exists n.+1=> //; exists n; first exact: ltnSn.
  exact: (hC n).1 x hx.
Qed.
