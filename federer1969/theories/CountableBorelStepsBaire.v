(** Federer (1969), 2.2.15, p. 71, sufficiency of the target criterion: a
    countable Borel step function is Baire when finite target sets can be
    approximated by curves. At each point its fixed label eventually belongs
    to every prefix, and the curve error tends to zero. This supplies part
    of the proof omitted in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground PointwiseLimit BaireFunctions
  BairePostcomposition RealBorelBaire BorelDiscreteIndexUP BorelDiscreteIndexBasic
  FiniteCurveApproximationUP CurveSequenceApproximationUP CurveSequenceApproximationSealed
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [curve_sequence_pointwise_limit]: supporting
    pointwise convergence for Federer 2.2.15, p. 71.
    At a fixed source point only its one natural label matters;
    no uniform bound on the range of labels is assumed. *)
Lemma curve_sequence_pointwise_limit (R : realType) (X : Type) (Y : metricType R)
    (y : nat -> Y) (c : nat -> real_line_metric R -> Y) (t : nat -> nat -> R)
    (q : X -> nat) : is_curve_sequence_approximation y c t ->
  is_pointwise_limit (fun n x => c n (t n (q x))) (y \o q).
Proof.
move=> h x V hV.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (y (q x)) V) hV.
have [N hN] := positive_reciprocal_nat_small he.
exists (maxn N (q x)); first exact Logic.I.
move=> n hn0.
have hn1 : (maxn N (q x) <= n)%N := hn0.
move: hn1; rewrite geq_max; move=> /andP[hn hi]; apply: hb.
have hd := curve_sequence_error h hi.
have hmon : (((n.+1)%:R : R)^-1) <= (((N.+1)%:R : R)^-1).
  have hnpos : (0 : R) < n.+1%:R by rewrite ltr0n.
  have hNpos : (0 : R) < N.+1%:R by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ hnpos hNpos) ler_nat.
exact: lt_trans hd (le_lt_trans hmon hN).
Qed.

(** Source for [countable_borel_step_baire]: supporting
    countable-range step in the sufficiency of Federer 2.2.15,
    p. 71. Real-valued Borel parameter maps are Baire;
    continuous curve postcomposition and pointwise closure finish
    the proof. Only the index fibres must be Borel. *)
Theorem countable_borel_step_baire (R : realType) (X : metricType R) (Y : metricType R)
    (y : nat -> Y) (q : X -> nat) :
  has_finite_curve_approximation Y -> has_borel_index_fibres q ->
  is_baire_function (y \o q).
Proof.
move=> h hq.
pose w := @CurveSequenceApproximation.value R Y y h.
have hw := @CurveSequenceApproximation.laws R Y y h.
apply: (@baire_function_pointwise_limit R X Y (fun n x => w.1 n (w.2 n (q x))) (y \o q)).
- move=> n.
  pose g (x : X) : real_line_metric R := w.2 n (q x).
  have hg : is_baire_function g.
    apply: real_borel_function_baire.
    exact: (@borel_function_of_discrete_index X [the topologicalType of real_line_metric R]
      q (w.2 n) hq).
  have hh := @baire_continuous_postcomposition R X [the metricType R of real_line_metric R]
    Y (w.1 n) (@curve_sequence_continuous R Y y w.1 w.2 hw n) g hg.
  exact hh.
- exact: curve_sequence_pointwise_limit hw.
Qed.
