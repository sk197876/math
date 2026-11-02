(** Federer (1969), 3.2.31, pp. 268–269: supporting
    countable rectifiability of the positive fibre-mass locus.
    Positive reciprocal thresholds give a countable union of
    the finite rectifiable threshold sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  HausdorffMeasure HausdorffFibreCutoffs MeasureUP MeasureBasic RectifiableSetUP
  CountablyMeasureRectifiableOperations CompactFibreThresholdRectifiability ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section CompactPositiveFibres.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [compact_positive_fibre_locus_countably_rectifiable]:
    supporting countable-compact-chart reduction in Federer 3.2.31,
    p. 269. The positive fibre locus is the union of closed
    reciprocal-threshold sets. Its total mass may be infinite;
    only countable measure rectifiability is concluded. *)
Theorem compact_positive_fibre_locus_countably_rectifiable (F:X->Y) (K:set X) L k mu:
  (0<v)%N ->(0<mu)%N ->m.+1=(k+mu)%N ->
  is_metric_lipschitz_bound setT F L ->compact K ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R Y mu) mu
    [set y|0<hausdorff_fibre_mass F K k y].
Proof.
move=>hv hmu hDim hLip hK.
pose t j:=(((j.+1)%:R:R)^-1)%R.
have ht j:(0<t j)%R by rewrite /t invr_gt0 ltr0n.
pose Z j:set Y:=[set y|(t j)%:E<=hausdorff_fibre_mass F K k y].
have hZ j:is_countably_measure_m_rectifiable (@hausdorff_measure R Y mu) mu (Z j).
  exact (@compact_fibre_threshold_rectifiable R m v F K L k mu (t j)
    hv hmu hDim (ht j) hLip hK).2.1.
have hUnion:[set y:Y|0<hausdorff_fibre_mass F K k y]=\bigcup_j Z j.
  apply/seteqP; split=>y.
  - move=>hy; change (is_true (0<hausdorff_fibre_mass F K k y)) in hy.
    case hValue:(hausdorff_fibre_mass F K k y)=>[a| |] in hy *; last by [].
    + have ha:(0<a)%R:=hy.
      have [j hj]:=positive_reciprocal_nat_small ha.
      exists j=>//; change (is_true ((t j)%:E<=hausdorff_fibre_mass F K k y)).
      rewrite hValue lee_fin; exact (ltW hj).
    + exists 0%N=>//; change (is_true ((t 0%N)%:E<=hausdorff_fibre_mass F K k y)).
      by rewrite hValue leey.
  - move=>[j _ hj].
    apply:lt_le_trans _ hj; by rewrite lte_fin.
rewrite hUnion.
exact (@countably_measure_rectifiable_countable_union R Y [the choiceType of (nat:Type)]
  (@hausdorff_measure R Y mu) mu setT Z (@hausdorff_measure_is_measure R Y mu)
  (countableP _) (fun j _=>hZ j)).
Qed.
End CompactPositiveFibres.
