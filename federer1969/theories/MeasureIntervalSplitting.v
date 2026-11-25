(** Federer (1969), 2.4.10, p. 85, last display: additivity across adjacent
    half-open intervals, provided the lower half-line through the dividing
    point is measurable. The proof below uses exactly that half-line
    premise; measurability of the two interval sets is not added. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialZeroExtensionLaws MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureIntegralSplitting MeasureSubsetIntegral MeasureIntervalIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [half_open_interval_split_sets]: the two
    set identities underlying the final display of Federer
    2.4.10, p. 85, including coincident and infinite endpoints. *)
Lemma half_open_interval_split_sets (R : realType) (X : Type)
    (coordinate : X -> \bar R) a b c :
  a <= b -> b <= c ->
  measure_half_open_interval coordinate a c `&` [set x | coordinate x <= b] =
    measure_half_open_interval coordinate a b /\
  measure_half_open_interval coordinate a c `\` [set x | coordinate x <= b] =
    measure_half_open_interval coordinate b c.
Proof.
move=> hab hbc; split; apply/seteqP; split=> x.
- move=> [/andP[hax hxc] hxb]; by apply/andP; split.
- move=> /andP[hax hxb]; split=> //; apply/andP; split=> //; exact: le_trans hxb hbc.
- move=> [/andP[hax hxc] hn]; apply/andP; split=> //.
  rewrite ltNge; apply/negP; exact hn.
- move=> /andP[hbx hxc]; split.
  + apply/andP; split=> //; exact: le_lt_trans hab hbx.
  + by move=> hxb; move: hbx; rewrite ltNge hxb.
Qed.

(** Source for [measure_interval_integral_split]: direct final
    additive formula of Federer 2.4.10, p. 85,
    as an equivalence of defined integral values. Infinite values
    are allowed when their partial sum is defined. The coordinate
    formulation covers both printed ambient spaces. *)
Theorem measure_interval_integral_split (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (coordinate : X -> \bar R)
    (a b c : \bar R) (f : partial_function X (extended_real_line R)) z :
  a <= b -> b <= c -> measure_measurable mu [set x | coordinate x <= b] ->
  (is_measure_interval_integral mu coordinate a c f z <-> exists u v,
    is_measure_interval_integral mu coordinate a b f u /\
    is_measure_interval_integral mu coordinate b c f v /\ extended_add u v=Some z).
Proof.
move=> hab hbc hB.
pose H := [set x | coordinate x <= b].
pose F := partial_function_zero_extension (0 : extended_real_line R) (measure_half_open_interval coordinate a c) f.
have [hleft hright] := @half_open_interval_split_sets R X coordinate a b c hab hbc.
have hl x y : partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) H F) x y <->
    partial_function_graph (partial_function_zero_extension (0 : extended_real_line R)
      (measure_half_open_interval coordinate a b) f) x y.
  by rewrite /F partial_zero_extension_intersection_graph setIC hleft.
have hr x y : partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) (~` H) F) x y <->
    partial_function_graph (partial_function_zero_extension (0 : extended_real_line R)
      (measure_half_open_interval coordinate b c) f) x y.
  by rewrite /F partial_zero_extension_intersection_graph setIC -setDE hright.
have hi := @measure_integral_measurable_split R X mu hm H F z hB.
split.
- move=> hz; have [u [v [hu [hv huv]]]] := hi.1 hz; exists u,v; split.
  + exact: measure_integral_graph_equivalent hl hu.
  + split=> //; exact: measure_integral_graph_equivalent hr hv.
- move=> [u [v [hu [hv huv]]]]; apply: hi.2; exists u,v; split.
  + apply: (@measure_integral_graph_equivalent R X mu _ _ u _ hu)=> x y; exact: iff_sym (hl x y).
  + split=> //; apply: (@measure_integral_graph_equivalent R X mu _ _ v _ hv)=> x y; exact: iff_sym (hr x y).
Qed.
