(** Federer (1969), 3.3.4, p. 289:
    fixed positive-radius/aperture coordinate costs
    have open strict superlevels. Apply the
    actual open-fibre argument of 3.3.2
    to the original arbitrary source A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm EuclideanBlockLinearMaps
  StructureConeUP StructureCoordinateCones StructureCoordinateGrowth
  StructureCoordinateIncidenceOpen StructureWeightedOpenFibre
  EuclideanClosedBallCompact LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_coordinate_cost_superlevel_open]:
    the open-cost step behind B_j/C_j
    measurability in Federer 3.3.4, p. 289,
    by 3.3.2, pp. 287–288. Actual
    joint frame evaluation, strict coordinate
    inequalities and closed-measurable compact-inner
    approximation discharge every topological and
    measure premise. No assumption on A is used. *)
Theorem structure_coordinate_cost_superlevel_open (R:realType) m k
    (P:topologicalType)
    (f:P->{linear R_n R (m+k)->R_n R (m+k)})
    (phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k))) (j:'I_k) (r s b:R):
  continuous (fun z:P*inner_metric_space (@euclidean_inner_productP R (m+k))=>
    (f z.1 (z.2-a):inner_metric_space (@euclidean_inner_productP R (m+k)))) ->
  is_structure_measure phi ->0<r ->0<s ->
  open [set p:P|(b%:E<structure_coordinate_cost phi A a (f p) j r s)%E].
Proof.
move=>hF [hPhi hClosed] hr hs.
pose E:=inner_metric_space (@euclidean_inner_productP R (m+k)).
pose w:=(r^-1)^+m*(s^-1)^+m.
have hw:0<w by rewrite /w mulr_gt0 // exprn_gt0 // invr_gt0.
pose U:set (P*E):=[set z|inner_norm (@euclidean_inner_productP R (m+k)) (z.2-a)<r /\
  ((s^-1)^+2-1)*
    (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f z.1 (z.2-a))))^+2<
    ((@euclidean_last_block R m k (f z.1 (z.2-a))) j)^+2].
have hU:open U:=@structure_coordinate_incidence_open R m k P
  (fun z:P*E=>(f z.1 (z.2-a):E)) a j r s hF.
have hCost p:structure_coordinate_cost phi A a (f p) j r s=
    (w%:E*phi (A `&` [set x|U (p,x)]))%E.
  rewrite /structure_coordinate_cost /structure_coordinate_cone.
  have hSet:[set x:E|A x /\ ((inner_norm (@euclidean_inner_productP R (m+k)) (x-a))%:E<r%:E)%E /\
    ((s^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f p (x-a))))^+2<
      ((@euclidean_last_block R m k (f p (x-a))) j)^+2]=A `&` [set x|U (p,x)].
    apply/seteqP; split=>x [hA [hR hAngle]]; split=>//; split=>//;
      by move:hR; rewrite lte_fin.
  by rewrite hSet -muleA -EFinM -/w muleC.
have hEqual:[set p:P|(b%:E<structure_coordinate_cost phi A a (f p) j r s)%E]=
    [set p:P|(b%:E<w%:E*phi (A `&` [set x|U (p,x)]))%E].
  apply/seteqP; split=>p;
    change ((b%:E<structure_coordinate_cost phi A a (f p) j r s)%E ->
      (b%:E<w%:E*phi (A `&` [set x|U (p,x)]))%E) ||
    change ((b%:E<w%:E*phi (A `&` [set x|U (p,x)]))%E ->
      (b%:E<structure_coordinate_cost phi A a (f p) j r s)%E);
    by rewrite hCost.
rewrite hEqual.
have hProper:metric_boundedly_compact [the metricType R of E].
  move=>c t _; exact:(@euclidean_closed_metric_ball_compact R (m+k) c t).
exact:(@structure_weighted_open_fibre_superlevel R P E phi A a U w b
  hPhi hProper hClosed hU hw).
Qed.
