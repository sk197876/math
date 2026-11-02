(** Federer (1969), 2.10.28(4), pp. 192–193: existence of Phi(J,n) with its
    specified equal-cost length, spacing and interval sets. Use the already
    sealed scalar radius, then a finite image of the n ordinal indices. This
    construction is a witness only and will be hidden behind opaque module
    ascription. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter MetricDiameterReal
  ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_family_exists]: supporting
    proved existence of Phi(J,n) in
    2.10.28(4), p. 192. The parent
    has positive diameter and n>=2; the
    interval family is characterised by its
    laws, without assuming its later specialness. *)
Theorem equal_cost_interval_family_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) n :
  0<fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)) ->
  (2<=n)%N -> exists F, is_equal_cost_interval_family h J n F.
Proof.
move=> hJpos hn; have [a [b [hab hJ]]] := set_valP J.
have hd : 0<b-a by move: hJpos; rewrite hJ (extended_metric_diameter_segment hab).
pose s := @cantor_split_radius R h hg (b-a) n hd hn.
have hs := @cantor_split_radius_specification R h hg (b-a) n hd hn.
pose t := cantor_split_spacing (b-a) n s.
have hspos : 0<s := (cantor_split_radius_bounds hs).1.
have hchild (i : 'I_n) : is_compact_real_interval
    (`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R)).
  exists (a+i%:R*t),(a+i%:R*t+s); split=> //; lra.
pose child (i : 'I_n) : compact_real_intervals R :=
  Sub (`[a+i%:R*t,a+i%:R*t+s] : set (real_line_metric R)) (mem_set (hchild i)).
pose F : {fset compact_real_intervals R} := [fset child i | i in enum 'I_n].
exists F; split=> //.
exists a,b,s,t; split; first exact hJ.
split; first exact hd.
split; first exact hs.
split; first by [].
move=> S; split.
- move=> /imfsetP[i hi ->]; exists (val i); split; first exact: ltn_ord.
  by [].
- move=> [i [hi hSi]].
  pose o : 'I_n := Ordinal hi.
  apply/imfsetP; exists o; first exact: mem_enum.
  apply: val_inj; exact hSi.
Qed.
