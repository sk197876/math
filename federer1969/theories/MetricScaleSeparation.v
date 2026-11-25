(** Federer (1969), 2.10.1, p. 170: sufficiently fine approximating covers
    cannot meet both separated sets. Source context and role in the 2.5.10
    example: MetricScaleEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumRestriction
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_envelope_separated_bound]: the displayed
    separated-set inequality in Federer 2.10.1, p. 170 A real positive lower
    bound for cross distances suffices; the diameter cutoff may be any
    smaller extended real. *)
Theorem metric_scale_envelope_separated_bound (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R)
    (A B : set X) (e : R) :
  is_metric_scale_envelope S cost delta nu ->
  (forall j, 0<=cost j) -> delta<e%:E ->
  (forall x, A x -> forall y, B y -> (e<=mdist x y)%R) ->
  nu A+nu B<=nu (A `|` B).
Proof.
move=> hn hc hde hsep.
apply: (metric_scale_envelope_greatest hn)=> G hG hd hcov.
pose H := [set j | exists x, A x /\ S j x].
have hGA : countable (G `&` H).
  apply: (sub_countable _ hG); apply: subset_card_le=> j [hj _]; exact hj.
have hGB : countable (G `\` H).
  apply: (sub_countable _ hG); apply: subset_card_le=> j [hj _]; exact hj.
have hAcov : A `<=` \bigcup_(j in G `&` H) S j.
  move=> x hx; have [j hj hSj] := hcov x (or_introl hx).
  exists j=> //; split=> //; by exists x.
have hBcov : B `<=` \bigcup_(j in G `\` H) S j.
  move=> y hy; have [j hj hSj] := hcov y (or_intror hy).
  exists j=> //; split=> //.
  move=> [x [hx hSx]].
  have hp := @metric_diameter_upper R X (S j) (extended_metric_diameter (S j))
    (extended_metric_diameter_specification (S j)) x y hSx hSj.
  have heb : e%:E<=(mdist x y)%:E by rewrite lee_fin; exact: hsep x hx y hy.
  have he : e%:E<=delta := le_trans heb (le_trans hp (hd j hj)).
  by move: hde; rewrite ltNge he.
have hA := @metric_scale_envelope_lower R X J S cost delta nu hn A (G `&` H)
  hGA (fun j hj => hd j hj.1) hAcov.
have hB := @metric_scale_envelope_lower R X J S cost delta nu hn B (G `\` H)
  hGB (fun j hj => hd j hj.1) hBcov.
have h := leeD hA hB.
by rewrite -(@nonnegative_sum_split R J G H cost (fun j _ => hc j)) in h.
Qed.
