(** Federer (1969), 3.3.2, pp. 287–288: every fixed
    positive-radius positive-aperture strict cost superlevel is open.
    Restriction to the original arbitrary A preserves measurability
    of closed sets; no measurable hull or local-finiteness premise
    replaces the printed standing assumption. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanClosedBallCompact
  LipschitzFunctionCompact MeasureUP MeasureRestriction StructureConeUP StructureCone
  StructureProjectionKernel StructureConeDensityUP StructureConeOpen
  StructureOpenFibreMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_cost_superlevel_open]: the
    open strict-superlevel assertion in the proof of Federer
    3.3.2, p. 288, for each fixed r,s>0. Taking their
    union gives the projected open sets of the corrected
    proof. A remains completely arbitrary. *)
Theorem structure_cone_cost_superlevel_open (R:realType) n m
    (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (r s b:R):
  is_structure_measure phi ->0<r ->0<s ->
  open [set z|(b%:E<structure_cone_cost hmn phi A z r s)%E].
Proof.
move=>[hm hClosed] hr hs.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=(E*euclidean_projection_space R n m)%type.
pose mu:=measure_restrict phi A.
have hMu:is_measure mu:=measure_restrict_is_measure hm A.
have hMuClosed C:closed C ->measure_measurable mu C.
  move=>hC; exact:(measure_restrict_measurable A (hClosed C hC)).
pose w:=((r^-1)^+m*(s^-1)^+m)%R.
have hw:0<w by rewrite /w mulr_gt0 // exprn_gt0 // invr_gt0.
pose U:set (P*E):=[set z|structure_cone (structure_projection_kernel hmn z.1.2)
  z.1.1 r%:E s z.2].
have hU:open U:=@structure_cone_incidence_open R n m hmn r s.
have hCost z:structure_cone_cost hmn phi A z r s=
    (((w^-1)^-1)%:E*mu [set x|U (z,x)])%E.
  rewrite invrK.
  change ((mu [set x|U (z,x)]*((r^-1)^+m)%:E*((s^-1)^+m)%:E)%E=
    (w%:E*mu [set x|U (z,x)])%E).
  by rewrite -muleA -EFinM -/w muleC.
have he:[set z:P|(b%:E<structure_cone_cost hmn phi A z r s)%E]=
    [set z:P|((w^-1*b)%R)%:E<mu [set x|U (z,x)]]%E.
  apply/seteqP; split=>z;
    change ((b%:E<structure_cone_cost hmn phi A z r s)%E ->
      (((w^-1*b)%R)%:E<mu [set x|U (z,x)])%E) ||
    change ((((w^-1*b)%R)%:E<mu [set x|U (z,x)])%E ->
      (b%:E<structure_cone_cost hmn phi A z r s)%E);
    by rewrite hCost lte_pdivlMl ?invr_gt0 // -EFinM.

rewrite he.
have hProper:metric_boundedly_compact [the metricType R of E].
  move=>a t _; exact:(@euclidean_closed_metric_ball_compact R n a t).
exact:(@structure_open_fibre_mass_superlevel R [the topologicalType of P]
  [the metricType R of E] mu (0:E) U (w^-1*b) hMu hProper hMuClosed hU).
Qed.
