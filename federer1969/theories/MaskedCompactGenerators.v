(** Federer (1969), 2.10.22, pp. 184–185: compact row factors for covers
    with inactive positions. A Boolean flag and a compact-set datum form a
    compact product factor; a false flag contributes the empty set and cost
    zero. The stored compact datum is then irrelevant, and no empty set is
    inserted into F. This makes finite covers compatible with the compact
    array argument. Source context and cost-order proof route:
    SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric HausdorffDistance
  HausdorffCompactNeighborhood MetricScaleOptionalCover SummableCostEnumerationUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [masked_compact_set]: supporting active
    set of a compact cover position in 2.10.22,
    pp. 184–185. A false flag is an inactive
    empty contribution, not a member of F. *)
Definition masked_compact_set (R : realType) (X : metricType R)
    (p : bool*compact_hausdorff_space X) : set X := if p.1 then val p.2 else set0.

(** Source for [masked_compact_cost]: supporting cost
    of a compact cover position in 2.10.22,
    pp. 184–185. False flags have auxiliary cost zero. *)
Definition masked_compact_cost (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (p : bool*compact_hausdorff_space X) : R :=
  if p.1 then c p.2 else 0.

(** Source for [optional_compact_point]: supporting
    compact-factor encoding of the selected optional
    cover in 2.10.22, pp. 184–185. The
    supplied default is irrelevant at inactive positions. *)
Definition optional_compact_point (R : realType) (X : metricType R)
    (d : compact_metric_set X) (o : option (compact_metric_set X)) : bool*compact_hausdorff_space X :=
  if o is Some C then (true,C) else (false,d).

(** Source for [optional_compact_setE]: supporting
    agreement with the actual optional cover in
    2.10.22, pp. 184–185. *)
Lemma optional_compact_setE (R : realType) (X : metricType R)
    (d : compact_metric_set X) o :
  masked_compact_set (optional_compact_point d o)=optional_generator_set (fun C=>val C) o.
Proof. by case: o. Qed.

(** Source for [optional_compact_costE]: supporting
    agreement of the compact-factor and optional
    covering costs in 2.10.22, pp. 184–185. *)
Lemma optional_compact_costE (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) (d : compact_metric_set X) o :
  masked_compact_cost c (optional_compact_point d o)=optional_generator_cost c o.
Proof. by case: o. Qed.

(** Source for [masked_compact_cost_continuous]: supporting
    coordinate cost continuity for the compact-array
    extraction in 2.10.22, pp. 184–185.
    The Boolean flag has its discrete topology. *)
Theorem masked_compact_cost_continuous (R : realType) (X : metricType R)
    (c : compact_metric_set X -> R) :
  continuous (fun C : compact_hausdorff_space X => (c C : real_line_metric R)) ->
  continuous (fun p : bool*compact_hausdorff_space X => (masked_compact_cost c p : real_line_metric R)).
Proof.
move=> hc [b C] W hW; case: b hW=> hW.
- exists ([set true], c @^-1` W).
  - split; [exact: discrete_set1|exact: hc C W hW].
  - move=> [b D] [hb hD].
    have he : b=true := hb; by rewrite /masked_compact_cost /= he.
- exists ([set false], setT).
  - split; [exact: discrete_set1|exact: filterT].
  - move=> [b D] [hb hD].
    have he : b=false := hb; rewrite /masked_compact_cost /= he; exact: nbhs_singleton hW.
Qed.

(** Source for [masked_compact_open_neighborhood]: supporting
    containment of every finite prefix of source
    cover positions in neighbourhoods of its limit,
    2.10.22, p. 185. Inactive limit positions
    have the empty neighbourhood available. *)
Theorem masked_compact_open_neighborhood (R : realType) (X : metricType R)
    (p : bool*compact_hausdorff_space X) (V : set X) :
  open V -> masked_compact_set p `<=` V ->
  nbhs p [set q | masked_compact_set q `<=` V].
Proof.
move=> hV hPV; case: p hPV=> [[|] D] hPV.
- have [e [he hbound]] := hausdorff_compact_open_neighborhood hV hPV.
  exists ([set true], ball D e).
  - split; [exact: discrete_set1|exact: nbhsx_ballx D e he].
  - move=> [b C] [hb hC].
    have hflag : b=true := hb.
    rewrite /masked_compact_set /= hflag.
    apply: hbound; change (is_true (hausdorff_distance D C<e)) in hC; exact hC.
- exists ([set false], setT).
  - split; [exact: discrete_set1|exact: filterT].
  - move=> [b C] [hb hC].
    have hflag : b=false := hb; rewrite /masked_compact_set /= hflag.
    by move=> x [].
Qed.
