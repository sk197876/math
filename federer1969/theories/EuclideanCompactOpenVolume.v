(** Supporting outer approximation for the open convex alternative in
    Federer (1969), 2.10.4(2), p. 172. Compact projected images have open
    neighbourhoods of arbitrarily close Lebesgue measure. Derive this from
    the proved Borel regular approximation of 2.2.3, p. 62, and
    finite-dimensional Lebesgue compact finiteness from 2.7.16, pp. 134–135.
    This is a proof ingredient, not an extra printed assertion of 2.10.4.
    Source context: ProjectedVolumeGaugeUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueHaar EuclideanLebesgueBoxes BorelRegularApproximation
  BorelRegularMeasureUP TopologicalBorel MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_compact_open_volume_bound]:
    supporting strict-cost neighbourhoods of compact
    projected images for Federer 2.10.4(2), p. 172.
    Empty compact sets and dimension zero are included;
    the upper bound is finite and strictly above the
    actual compact-set measure. *)
Theorem euclidean_compact_open_volume_bound (R : realType) (m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R m))) (b : R) :
  compact K -> euclidean_lebesgue_measure m K<b%:E ->
  exists U, open U /\ K `<=` U /\ euclidean_lebesgue_measure m U<b%:E.
Proof.
move=> hK hb.
have hm := euclidean_lebesgue_is_measure R m.
have hr := euclidean_lebesgue_borel_regular R m.
have hf : euclidean_lebesgue_measure m K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm K)).
  exact: lt_trans hb (ltry b).
pose v := fine (euclidean_lebesgue_measure m K).
have hv : (v<b)%R by move: hb; rewrite -(fineK hf) lte_fin.
pose e := ((b-v)/2)%R.
have he : (0<e)%R by rewrite /e divr_gt0 // subr_gt0.
have [ho hc hcov] := @euclidean_ball_cover R m.
have hfin n : euclidean_lebesgue_measure m (@euclidean_open_ball_sequence R m n) < +oo.
  have [C hC hs] := hc n.
  exact: le_lt_trans (measure_mono hm hs) (euclidean_compact_finite hC).
have hKm : measure_measurable (@euclidean_lebesgue_measure R m) K.
  apply: (borel_regular_borel_measurable hm hr).
  exact: closed_borel_set (compact_closed (@metric_hausdorff R
    (inner_metric_space (@euclidean_inner_productP R m))) hK).
have hcoverK : K `<=` \bigcup_n (@euclidean_open_ball_sequence R m n).
  move=> x _; have [k hk] := hcov x; by exists k.
have [U [hU [hKU herror]]] := @borel_regular_open_approximation R
  (inner_metric_space (@euclidean_inner_productP R m)) (@euclidean_lebesgue_measure R m)
  hm hr K (@euclidean_open_ball_sequence R m) e hKm
  (fun n => conj (ho n) (hfin n)) hcoverK he.
exists U; split=> //; split=> //.
have hcover : U `<=` K `|` (U `\` K).
  move=> x hx; case: (pselect (K x))=> [hk|hk]; [by left|right; by split].
have hbnd := measure_binary_cover hm hcover.
have hsum : euclidean_lebesgue_measure m K+euclidean_lebesgue_measure m (U `\` K)
    <=(v+e)%R%:E.
  rewrite -(fineK hf) EFinD; exact: leeD (lexx _) (ltW herror).
apply: le_lt_trans (le_trans hbnd hsum) _; rewrite lte_fin /e; lra.
Qed.
