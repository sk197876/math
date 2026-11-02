(** Federer (1969), 2.4.12, p. 87, finite-image density: private finite
    nearest-point partitions supporting the dominated approximation
    argument. The recursion is only a witness of the abstract approximation
    laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import TopologicalBorel BorelFamilyBasic BorelDiscreteIndexUP MetricNearestComparison FiniteNearestApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Variable Y : metricType R.
Variable y : nat -> Y.

(** Source for [finite_nearest_index]: private existence construction
    for finite-image approximation in Federer 2.4.12, p. 87.
    Keep a closest earlier candidate unless the new one is at least
    as close. No uniqueness of a closest point is assumed. *)
Fixpoint finite_nearest_index (n : nat) (x : Y) : nat :=
  if n is k.+1 then
    if mdist x (y k.+1) <= mdist x (y (finite_nearest_index k x)) then k.+1
    else finite_nearest_index k x
  else 0%N.

(** Source for [finite_nearest_index_bounded]: finite-image support
    for Federer 2.4.12, p. 87. The recursion never chooses
    a candidate outside the finite prefix. *)
Lemma finite_nearest_index_bounded n x : (finite_nearest_index n x <= n)%N.
Proof.
elim: n=> [|n ih] //=; case: ifP=> _; first exact: leqnn.
exact: leq_trans ih (leqnSn n).
Qed.

(** Source for [finite_nearest_index_minimal]: pointwise error control
    for the finite-image approximation in Federer 2.4.12, p. 87.
    Every finite prefix has a nearest candidate, without compactness
    of the ambient metric space. *)
Lemma finite_nearest_index_minimal n x i : (i <= n)%N ->
  mdist x (y (finite_nearest_index n x)) <= mdist x (y i).
Proof.
elim: n=> [|n ih] in i *.
- by rewrite leqn0=> /eqP ->.
- rewrite leq_eqVlt; move=> /orP[/eqP ->|hi] /=.
  + case: ifP=> h; first exact: lexx.
    have hh : mdist x (y (finite_nearest_index n x)) < mdist x (y n.+1) by rewrite ltNge h.
    exact: ltW hh.
  + case: ifP=> h; last exact: ih hi.
    exact: le_trans h (ih i hi).
Qed.

(** Source for [finite_nearest_switch_borel]: supporting measurable choice
    between the new candidate and the previous finite partition for Federer
    2.4.12, p. 87 A countable union of Borel fibres reduces the varying old
    candidate to the fixed-point distance comparison. *)
Lemma finite_nearest_switch_borel n : has_borel_index_fibres (finite_nearest_index n) ->
  borel_set [set x : Y | mdist x (y n.+1) <= mdist x (y (finite_nearest_index n x))].
Proof.
move=> hf.
pose A i := [set x : Y | finite_nearest_index n x = i] `&`
  [set x : Y | mdist x (y n.+1) <= mdist x (y i)].
have he : [set x : Y | mdist x (y n.+1) <= mdist x (y (finite_nearest_index n x))] =
    \bigcup_(i in @setT nat) A i.
  apply/seteqP; split=> x.
  - move=> hx; exists (finite_nearest_index n x)=> //; by split.
  - by move=> [i _ [hi hh]]; rewrite /= hi.
rewrite he; apply: (@borel_set_countable_union Y nat setT A (countableP _))=> i _.
exact: (borel_family_binary_intersection (borel_sets_family Y)) (hf i) (metric_nearer_set_borel _ _).
Qed.

(** Source for [finite_nearest_index_fibres]: Borel finite partitions
    supporting Federer 2.4.12, p. 87. The induction keeps
    the old fibres off the switch set and assigns the switch set
    to the newly selected label. *)
Lemma finite_nearest_index_fibres n : has_borel_index_fibres (finite_nearest_index n).
Proof.
elim: n=> [|n ih] k.
- have [hk|hk] := eqVneq 0%N k.
  + have he : [set x : Y | finite_nearest_index 0 x = k] = setT by apply/seteqP; split.
    rewrite he; exact: open_borel_set openT.
  + have he : [set x : Y | finite_nearest_index 0 x = k] = set0.
      apply/seteqP; split; last by move=> x [].
      move=> x hx; change (0%N=k) in hx; exfalso; move: hk; by rewrite hx eqxx.
    rewrite he; exact: open_borel_set open0.
- pose A := [set x : Y | mdist x (y n.+1) <= mdist x (y (finite_nearest_index n x))].
  have hA : borel_set A := finite_nearest_switch_borel ih.
  have [hk|hk] := eqVneq n.+1 k.
  + have he : [set x : Y | finite_nearest_index n.+1 x = k] = A `|` ([set x : Y | finite_nearest_index n x = k] `\` A).
      apply/seteqP; split=> x; rewrite /finite_nearest_index -/finite_nearest_index /=;
        case: ifP=> hx.
      * by move=> _; left.
      * move=> hh; right; split=> //.
        move=> ha; change (is_true (mdist x (y n.+1) <= mdist x (y (finite_nearest_index n x)))) in ha.
        by rewrite ha in hx.
      * by move=> _.
      * move=> [ha|[hh _]]=> //; by move: hx; rewrite ha.
    rewrite he; exact: (borel_family_binary_union (borel_sets_family Y)) hA (borel_set_difference (ih k) hA).
  + have he : [set x : Y | finite_nearest_index n.+1 x = k] = [set x : Y | finite_nearest_index n x = k] `\` A.
      apply/seteqP; split=> x; rewrite /finite_nearest_index -/finite_nearest_index /=;
        case: ifP=> hx.
      * move=> hh; exfalso; move: hk; by rewrite hh eqxx.
      * move=> hh; split=> //.
        move=> ha; change (is_true (mdist x (y n.+1) <= mdist x (y (finite_nearest_index n x)))) in ha.
        by rewrite ha in hx.
      * by move=> [_ hn]; exfalso; apply: hn.
      * by move=> [hh _].
    rewrite he; exact: borel_set_difference (ih k) hA.
Qed.

(** Source for [finite_nearest_approximation_exists]: existence of
    the finite Borel nearest-point approximants supporting Federer
    2.4.12, p. 87. Downstream proofs use only these laws;
    this recursion is hidden by the sealing module. *)
Theorem finite_nearest_approximation_exists : exists q, is_finite_nearest_approximation y q.
Proof.
exists finite_nearest_index; constructor.
- exact: finite_nearest_index_bounded.
- exact: finite_nearest_index_fibres.
- exact: finite_nearest_index_minimal.
Qed.
End Construction.
