(** Federer (1969), 3.3.4, p. 289:
    a positive finite radius/aperture weight
    preserves the open strict mass superlevels
    in the proof of 3.3.2, pp. 287–288.
    Keep the original arbitrary source A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureRestriction StructureOpenFibreMass
  LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_weighted_open_fibre_superlevel]:
    the fixed-radius/aperture open superlevels
    supporting B_j and C_j in Federer
    3.3.4, p. 289. Positive scalar
    threshold conversion and the actual
    compact-inner open-fibre argument retain
    arbitrary A and infinite mass, with
    closed-set measurability as the only
    regularity premise on the original measure. *)
Theorem structure_weighted_open_fibre_superlevel (R:realType)
    (P:topologicalType) (X:metricType R) (phi:set X->\bar R)
    (A:set X) (a:X) (U:set (P*X)) (w b:R):
  is_measure phi ->metric_boundedly_compact X ->
  (forall C,closed C ->measure_measurable phi C) ->
  open U ->0<w ->
  open [set p:P|(b%:E<w%:E*phi (A `&` [set x|U (p,x)]))%E].
Proof.
move=>hPhi hX hClosed hU hw.
pose mu:=measure_restrict phi A.
have hMu:=measure_restrict_is_measure hPhi A.
have hMuClosed C:closed C ->measure_measurable mu C.
  move=>hC; exact:(measure_restrict_measurable A (hClosed C hC)).
have hThreshold p:(b%:E<w%:E*mu [set x|U (p,x)])%E=
    (((w^-1*b)%R)%:E<mu [set x|U (p,x)])%E.
  by rewrite -{1}(invrK w) lte_pdivlMl ?invr_gt0 // -EFinM.
have hEqual:[set p:P|(b%:E<w%:E*phi (A `&` [set x|U (p,x)]))%E]=
    [set p:P|((w^-1*b)%R)%:E<mu [set x|U (p,x)]]%E.
  apply/seteqP; split=>p;
    change ((b%:E<w%:E*mu [set x|U (p,x)])%E ->
      (((w^-1*b)%R)%:E<mu [set x|U (p,x)])%E) ||
    change ((((w^-1*b)%R)%:E<mu [set x|U (p,x)])%E ->
      (b%:E<w%:E*mu [set x|U (p,x)])%E);
    by rewrite hThreshold.
rewrite hEqual.
exact:(@structure_open_fibre_mass_superlevel R P X mu a U (w^-1*b)
  hMu hX hMuClosed hU).
Qed.
