(** Closed exterior-diameter constraint in Federer (1969), 2.10.32, p. 196.
    Pair the endpoints into the actual continuous exterior norm and apply
    the proved Hausdorff-closed universal endpoint bound. The normalised
    cost sublevel is equivalent to the endpoint bound mu divided by alpha(m)
    2^(-m), retaining the corrected factor in Federer's erratum p. 4, book
    p. 197 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric CompactSetDistanceProfile
  CompactHausdorffMetric RealMetricBackground ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter
  ExteriorEndpointContinuity ExteriorMeasureGauge HausdorffDiameterCost HausdorffClosedEndpointBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_exterior_endpoint_bound_family_closed]:
    supporting closedness of the exterior-product
    bound in 2.10.32, p. 196. Arbitrary
    natural exterior degree and ambient dimension
    are allowed in this continuity fact. *)
Lemma hausdorff_exterior_endpoint_bound_family_closed (R : realType) (n m : nat) (q : R) :
  closed [set K : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)) |
    forall a b : 'I_m -> R_n R n, (forall i, val K (a i)) -> (forall i, val K (b i)) ->
      exterior_difference_norm a b<=q].
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose H := compact_hausdorff_space E.
pose I := [the eqType of ('I_m*bool)%type].
have he : [set K : H | forall a b : 'I_m -> R_n R n,
      (forall i, val K (a i)) -> (forall i, val K (b i)) -> exterior_difference_norm a b<=q]=
    [set K : H | forall p : I -> E, (forall i, val K (p i)) -> paired_exterior_norm p<=q].
  apply/seteqP; split=> K hK.
  - move=> p hp; rewrite paired_exterior_normE.
    exact (hK (fun i=>p (i,false)) (fun i=>p (i,true))
      (fun i=>hp (i,false)) (fun i=>hp (i,true))).
  - move=> a b ha hb.
    pose p (i : I) : E := if i.2 then b i.1 else a i.1.
    have hp i : val K (p i) by case: i=> i []; [exact: hb|exact: ha].
    have hh := hK p hp; change (is_true (exterior_difference_norm a b<=q)) in hh.
    exact hh.
rewrite he.
exact (@hausdorff_continuous_endpoint_bounds_closed R E I
  (fun p=> (paired_exterior_norm p : real_line_metric R)) q
  (@paired_exterior_norm_continuous R n m)).
Qed.

(** Source for [hausdorff_exterior_cost_sublevel_closed]: direct
    closedness of the cost constraint defining C
    in 2.10.32, p. 196. Nonnegative mu
    includes the printed positive case and retains
    the zero-bound limit. The endpoint bound is
    mu divided by the full normalising coefficient. *)
Theorem hausdorff_exterior_cost_sublevel_closed (R : realType) (n m : nat) (mu : R) :
  0<=mu ->
  closed [set K : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)) |
    (exterior_diameter_cost m (val K)<=mu%:E)%E].
Proof.
move=> hmu.
pose H := compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)).
pose c := hausdorff_normalisation R m.
have hc : 0<c := hausdorff_normalisation_positive R m.
have hcE : (0<=c%:E)%E by rewrite lee_fin; exact: ltW hc.
have hq : 0<=mu/c by rewrite divr_ge0 //; exact: ltW hc.
have he : [set K : H | (exterior_diameter_cost m (val K)<=mu%:E)%E]=
    [set K : H | forall a b : 'I_m -> R_n R n,
      (forall i, val K (a i)) -> (forall i, val K (b i)) -> exterior_difference_norm a b<=mu/c].
  apply/seteqP; split=> K hK.
  - move=> a b ha hb.
    have hn := exterior_diameter_endpoint_upper (extended_exterior_diameter_specification m (val K)) ha hb.
    have hh := lee_wpmul2l hcE hn.
    change (is_true (((c*exterior_difference_norm a b)%:E<=exterior_diameter_cost m (val K))%E)) in hh.
    have hle := le_trans hh hK; rewrite lee_fin in hle.
    by rewrite ler_pdivlMr // mulrC.
  - have hs : (extended_exterior_diameter m (val K)<=(mu/c)%:E)%E.
      apply: (exterior_diameter_least_bound (extended_exterior_diameter_specification m (val K))).
      + by rewrite lee_fin.
      + move=> a b ha hb; rewrite lee_fin; exact: hK a b ha hb.
    have hh := lee_wpmul2l hcE hs.
    rewrite -EFinM mulrCA mulfV ?gt_eqF // mulr1 in hh.
    exact hh.
rewrite he; exact: hausdorff_exterior_endpoint_bound_family_closed.
Qed.
