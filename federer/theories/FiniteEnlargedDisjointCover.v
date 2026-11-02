(** Federer (1969), 2.10.24(2), p. 188: finite disjoint layers obtained from
    2.8.4, p. 143. The original members of a layer are disjoint; their
    controlled enlargements cover the target. The hats in the cover and cost
    estimate are retained explicitly. Source context:
    WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameter CoveringFamilyUP DiameterWeightLaws DiametricRegularityUP
  WeightedCoverSelectionUP WeightedCoverSelection DiameterEnlargements CaratheodoryWeakEnlargementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_enlarged_disjoint_cover]: supporting
    finite layer selection in 2.10.24(2), p. 188.
    This is the sealed 2.8.4 selection with diameter
    weights. Empty generators are excluded, as required
    by the erratum p. 3, book p. 143 line 17;
    zero-diameter nonempty generators remain eligible. *)
Theorem finite_enlarged_disjoint_cover (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X) (k d : R)
    (P : {fset set_type F}) :
  is_weak_caratheodory_enlargement F c E k ->
  (forall j, j \in P -> val j<>set0) ->
  (forall j, j \in P -> extended_metric_diameter (val j)<=d%:E) ->
  exists H : {fset set_type F}, (H `<=` P)%fset /\
    (forall i j, i \in H -> j \in H -> i!=j -> val i `&` val j=set0) /\
    (\bigcup_(j in [set` P]) val j) `<=` \bigcup_(j in [set` H]) E (val j).
Proof.
move=> hE hne hdiam.
pose Q : set (set X) := val @` [set` P].
have hQF : Q `<=` F by move=> S [j hj <-]; exact: set_valP.
have hQfinite : finite_set Q := finite_image val (finite_fset P).
have hQne S : Q S -> S<>set0 by move=> [j hj <-]; exact: hne.
have hQbound S : Q S -> metric_set_bounded S.
  move=> [j hj <-]; exact: le_lt_trans (hdiam j hj) (ltry d).
have [w hw] := @real_diameter_weight_exists R X Q hQbound.
have hwn := @diameter_weight_nonnegative R X Q w hw.
have hwb : exists M : R, forall S, Q S -> (w S<=M)%R.
  exists d=> S hS; have [j hj heq] := hS.
  have he := metric_diameter_unique (extended_metric_diameter_specification S) (hw S hS).
  have hh := hdiam j hj; by rewrite heq he lee_fin in hh.
have ht : (1<2 :> R)%R by rewrite ltr1n.
pose G := @weighted_cover_selection R X Q w 2 hQne hwn hwb ht.
have hG := @weighted_cover_selection_specification R X Q w 2 hQne hwn hwb ht.
pose Hset : set (set_type F) := [set j | G (val j)].
have hHPset : Hset `<=` [set` P].
  move=> j hj; have [i hi he] := weighted_selection_members hG hj.
  have heij : i=j by apply: val_inj.
  by rewrite -heij.
have hHfinite : finite_set Hset := sub_finite_set hHPset (finite_fset P).
have [H hH] := (@finite_fsetP [the choiceType of set_type F] Hset).1 hHfinite.
have hHP : (H `<=` P)%fset.
  apply/fsubsetP=> j hj; apply: hHPset; by rewrite hH.
have hcov : (\bigcup_(j in [set` P]) val j) `<=` \bigcup_(j in [set` H]) E (val j).
  move=> x [j hj hxj].
  have hjQ : Q (val j) by exists j.
  have [T [hT [hmeet hwt]]] := weighted_selection_dominates hG hjQ.
  have [i hi he] := weighted_selection_members hG hT.
  have hTG : G (val i) by rewrite he.
  exists i; first by rewrite -hH.
  apply: (@weak_enlargement_contains R X F c E k hE (val i) (set_valP i) x).
  exists (val j)=> //; split; first exact: set_valP.
  split; first by rewrite he.
  have hiQ : Q (val i) by exists i.
  have hjdia := metric_diameter_unique (extended_metric_diameter_specification (val j)) (hw _ hjQ).
  have hidia := metric_diameter_unique (extended_metric_diameter_specification (val i)) (hw _ hiQ).
  by rewrite hjdia hidia -EFinM lee_fin he.
exists H; split=> //; split=> // i j hi hj hij.
apply: (weighted_selection_disjoint hG).
- change (Hset i); by rewrite hH.
- change (Hset j); by rewrite hH.
move=> he; apply: (negP hij); apply/eqP; exact: val_inj he.
Qed.
