(** Federer (1969), 3.2.11, p. 249: the
    Borel-source reduction under Lebesgue measurability.
    Apply the finite sandwich of 2.2.3 to a countable
    finite-measure cover and unite the inner Borel cores. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  TopologicalBorel BorelRegularMeasureUP BorelRegularSandwich CountablyMeasurableUP
  CountablyMeasurableSubsets MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_measurable_borel_core]: the
    Borel reduction in Federer 3.2.11, p. 249,
    including infinite source mass. The discarded source is
    Lebesgue null; no Borelness of the original set is assumed. *)
Theorem euclidean_measurable_borel_core (R:realType) m
    (A:set (inner_metric_space (@euclidean_inner_productP R m))):
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists C,borel_set C /\C `<=` A /\euclidean_lebesgue_measure m (A `\` C)=0.
Proof.
move=>hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
have hCount:=@measurable_subset_countably_measurable R X mu hm A setT hA (fun x _=>Logic.I)
  (euclidean_lebesgue_countably_measurable R m).
have [F [hF [hUnion hFinite]]]:=hCount.
have hex B:exists C:set X,F B ->borel_set C /\C `<=` B /\mu (B `\` C)=0.
  case:(pselect (F B))=>hB; last by exists set0=>h; exfalso; exact:hB h.
  have [C [D [hC [hD [hCB [hBD hNull]]]]]]:=borel_regular_finite_sandwich hm
    (euclidean_lebesgue_borel_regular R m) (hFinite B hB).1 (hFinite B hB).2.
  exists C=>_; split=> //; split=> //.
  apply:(measure_null_subset hm _ hNull)=>x [hx hn]; by split; first exact:hBD.
have [C hC]:=choice hex.
pose D:set X:=\bigcup_(B in F) C B.
have hDB:borel_set D.
  apply:borel_set_countable_union; first exact hF.
  by move=>B hB; exact (hC B hB).1.
have hDA:D `<=` A.
  move=>x [B hB hx]; rewrite hUnion; exists B=> //; exact ((hC B hB).2.1 x hx).
have hExcess:A `\` D `<=` \bigcup_(B in F) (B `\` C B).
  move=>x [hx hn]; rewrite hUnion in hx; have [B hB hxB]:=hx.
  exists B=> //; split=> //; move=>hc; apply:hn; by exists B.
exists D; split=> //; split=> //.
apply:(measure_null_subset hm hExcess).
apply:(measure_null_countable_union hm hF)=>B hB; exact (hC B hB).2.2.
Qed.
