(** Federer (1969), 2.9.19, p. 164: finite real interval masses of the
    induced measures, their difference as g-increment and their sum bounded
    by s-increment. These supporting real witnesses are derived from finite
    measure values, not assumed as extra interval data. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures StieltjesDerivationClass
  StieltjesIntervalIncrements StieltjesClosedVariationBounds MeasureDerivationContext MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_finite_interval_masses]: supporting finite
    interval comparison in Federer 2.9.19, p. 164 At continuity endpoints,
    nonnegative finite real masses P,M represent the two induced measures on
    [a,b], satisfy P-M=g(b)-g(a), and have P+M<=s(b)-s(a). The sum bound and
    measure nonnegativity derive finiteness before any real subtraction is
    performed. *)
Lemma stieltjes_finite_interval_masses (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> a<b ->
  g @ a --> g a -> g @ b --> g b -> exists P M : R,
    psip `[a,b]= P%:E /\ psim `[a,b]= M%:E /\ 0<= P /\ 0<= M /\
    g b-g a= P-M /\ P+M<=arc_length (g : R -> real_line_metric R) b-
      arc_length (g : R -> real_line_metric R) a.
Proof.
move=> hg hp hab hca hcb.
have [hcP hcM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hmP := derivation_measure_law hcP; have hmM := derivation_measure_law hcM.
have hP0 := measure_nonnegative hmP `[a,b]; have hM0 := measure_nonnegative hmM `[a,b].
have hsum := @stieltjes_closed_pair_variation_bound R g psip psim a b hg hp (ltW hab) hca hcb.
have hsumfin := le_lt_trans hsum (@ltry R
  (arc_length (g : R -> real_line_metric R) b-arc_length (g : R -> real_line_metric R) a)).
have hPfin : psip `[a,b] \is a fin_num.
  rewrite (ge0_fin_numE hP0); exact: le_lt_trans (lee_paddr hM0 (lexx _)) hsumfin.
have hMfin : psim `[a,b] \is a fin_num.
  rewrite (ge0_fin_numE hM0); exact: le_lt_trans (lee_paddl hP0 (lexx _)) hsumfin.
pose P := fine (psip `[a,b]); pose M := fine (psim `[a,b]).
have hPE : psip `[a,b]= P%:E by rewrite /P fineK.
have hME : psim `[a,b]= M%:E by rewrite /M fineK.
have hP : 0<= P by move: hP0; rewrite hPE lee_fin.
have hM : 0<= M by move: hM0; rewrite hME lee_fin.
have hinc := @stieltjes_induced_pair_closed_interval_increment R g psip psim a b hg hp hab hca hcb.
rewrite hPE hME -EFinB in hinc.
have hincR : g b-g a= P-M := EFin_inj hinc.
have hsumR : P+M<=arc_length (g : R -> real_line_metric R) b-
    arc_length (g : R -> real_line_metric R) a.
  by move: hsum; rewrite hPE hME -EFinD lee_fin.
exists P,M; split=> //; split=> //; split=> //; split=> //; by split.
Qed.
