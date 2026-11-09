(** Federer (1969), 3.3.20, p. 308:
    existence and outer-measure laws of the original psi_j. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal.
From Federer Require Import EuclideanInnerProduct InnerMetric CompactIntervalGauge
  EuclideanIntervalRectangles FiniteCellHitMeasureUP FiniteCellHitMeasureExistence
  CriticalSquareHitMeasureUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_square_hit_measures_exist]: the
    literal finite hit counts give actual original
    auxiliary outer measures psi_j, as asserted in
    3.3.20, p. 308. Each weight is nonnegative;
    finite sums prove the outer-measure laws. No
    selected global auxiliary family is introduced. *)
Theorem critical_square_hit_measures_exist (R:realType)
    (G:nat->{fset (compact_real_intervals R*compact_real_intervals R)}):
  exists psi,is_critical_square_hit_measures G psi /\forall j,is_measure (psi j).
Proof.
have hExists j:exists mu,is_finite_cell_hit_measure (G j)
    (fun P=>euclidean_interval_rectangle P.1 P.2) (Num.sqrt 2/(4:R)^+j) mu /\is_measure mu.
  apply:finite_cell_hit_measure_exists.
  apply:divr_ge0;first exact:sqrtr_ge0.
  apply:ltW;by rewrite exprn_gt0 // ltr0n.
have [psi hPsi]:=choice hExists.
exists psi;split;[move=>j;exact:(hPsi j).1|move=>j;exact:(hPsi j).2].
Qed.

(** Source for [critical_square_hit_measures_are_measures]:
    every actual family with the independent printed
    psi_j laws satisfies the outer-measure laws,
    3.3.20, p. 308. The conclusion follows
    from finite-cell existence and uniqueness. *)
Lemma critical_square_hit_measures_are_measures (R:realType)
    (G:nat->{fset (compact_real_intervals R*compact_real_intervals R)}) psi:
  is_critical_square_hit_measures G psi ->forall j,is_measure (psi j).
Proof.
move=>hPsi j;apply:(finite_cell_hit_measure_is_measure _ (hPsi j)).
apply:divr_ge0;first exact:sqrtr_ge0.
apply:ltW;by rewrite exprn_gt0 // ltr0n.
Qed.
