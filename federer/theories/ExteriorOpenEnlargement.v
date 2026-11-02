(** Supporting open enlargement for Federer (1969), 2.10.3, p. 172. Close a
    finite-diameter generator, use compactness of its finite endpoint power
    and continuity of the actual exterior norm to control every nearby
    endpoint tuple, then thicken the original set by a sufficiently small
    positive radius. This expands the printed open-cover assertion without
    assuming continuity of a supremum operator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter ExteriorDiameterClosure
  ExteriorMeasureGauge ExteriorEndpointContinuity HausdorffDiameterCost EuclideanBoundedClosure
  MetricDiameter MetricOpenThickening CompactCoordinateNeighbourhood RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_gauge_open_enlargement]: supporting
    arbitrarily close-cost open generators for Federer
    2.10.3, p. 172. Preserve the target size cap
    simultaneously. The supremum need not be attained;
    a strict upper cost bound is enough. *)
Theorem exterior_gauge_open_enlargement (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (d t b : R) :
  A !=set0 -> 0<=d -> d<t -> (extended_metric_diameter A<=d%:E)%E ->
  (exterior_diameter_cost m A<b%:E)%E ->
  exists U : set (inner_metric_space (@euclidean_inner_productP R n)),
    open U /\ U !=set0 /\ A `<=` U /\
    (extended_metric_diameter U<=t%:E)%E /\ (exterior_diameter_cost m U<=b%:E)%E.
Proof.
move=> hA hd hdt hdiam hb.
pose K := closure A.
have hK : compact K := euclidean_bounded_set_closure_compact hA hdiam.
pose c : R := hausdorff_normalisation R m.
have hc : 0<c := hausdorff_normalisation_positive R m.
have hcE : (0<=c%:E)%E by rewrite lee_fin; exact: ltW hc.
have hbpos : 0<b.
  have hh := le_lt_trans (exterior_diameter_cost_nonnegative m A) hb.
  by move: hh; rewrite lte_fin.
have hcostK : exterior_diameter_cost m K=exterior_diameter_cost m A.
  by rewrite /K exterior_diameter_cost_closure.
pose P := [the topologicalType of (('I_m*bool)%type -> inner_metric_space (@euclidean_inner_productP R n))].
pose O : set P := [set p | paired_exterior_norm p<b/c].
have hF : continuous (fun p : P => (paired_exterior_norm p : real_line_metric R)) :=
  @paired_exterior_norm_continuous R n m.
have hO : open O.
  have ho : @open (real_line_metric R) [set x | x<b/c] := @open_lt R (b/c).
  apply: (@open_comp P (real_line_metric R)
    (fun p => (paired_exterior_norm p : real_line_metric R))
    [set x : real_line_metric R | x<b/c] _ ho).
  by move=> p _; exact: hF.
have hinside p : (forall i, K (p i)) -> O p.
  move=> hp.
  have hnorm := @exterior_diameter_endpoint_upper R n m K (extended_exterior_diameter m K)
    (fun i => p (i,false)) (fun i => p (i,true)) (extended_exterior_diameter_specification m K)
    (fun i => hp (i,false)) (fun i => hp (i,true)).
  have hh := lee_wpmul2l hcE hnorm.
  change (is_true (((c*paired_exterior_norm p)%:E<=exterior_diameter_cost m K)%E)) in hh.
  rewrite hcostK in hh; have hlt := le_lt_trans hh hb.
  rewrite lte_fin in hlt.
  change (is_true (paired_exterior_norm p<b/c)).
  by rewrite ltr_pdivlMr // mulrC.
have [e [he hTube]] := @compact_finite_power_neighbourhood R [the finType of ('I_m*bool)%type]
  (inner_metric_space (@euclidean_inner_productP R n)) K O hK hO hinside.
pose r := Order.min (e/2) ((t-d)/4).
have hr : 0<r by rewrite /r lt_min !divr_gt0 // ?ltr0n subr_gt0.
have hre : r<=e.
  have hh : r<=e/2 by rewrite /r ge_min lexx.
  lra.
have hrt : r<=(t-d)/4 by rewrite /r ge_min lexx orbT.
have hcap : d+r+r<t by lra.
pose U := metric_open_thickening A r.
have hAU : A `<=` U := metric_open_thickening_includes hr.
have hne : U !=set0 by have [x hx] := hA; exists x; exact: hAU x hx.
have hUK : U `<=` metric_open_thickening K e.
  move=> x [a ha hax]; exists a; first exact: subset_closure ha.
  exact: lt_le_trans hax hre.
have hUsup : (extended_exterior_diameter m U<=(b/c)%:E)%E.
  apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification m U)).
  - by rewrite lee_fin divr_ge0 //; exact: ltW hbpos || exact: ltW hc.
  - move=> a z ha hz.
    pose p (i : ('I_m*bool)%type) := if i.2 then z i.1 else a i.1.
    have hp i : metric_open_thickening K e (p i).
      case: i=> i s; case: s=> /=; [exact: hUK _ (hz i)|exact: hUK _ (ha i)].
    have hh := hTube p hp.
    change (is_true (exterior_difference_norm a z<b/c)) in hh.
    rewrite lee_fin; exact: ltW hh.
have hUcost : (exterior_diameter_cost m U<=b%:E)%E.
  have hh := lee_wpmul2l hcE hUsup.
  rewrite -EFinM mulrCA mulfV ?gt_eqF // mulr1 in hh.
  exact hh.
exists U; split; first exact: metric_open_thickening_open.
split=> //; split=> //; split=> //.
apply: le_trans (metric_open_thickening_diameter_bound hd (ltW hr) hdiam) _.
rewrite lee_fin; exact: ltW hcap.
Qed.
