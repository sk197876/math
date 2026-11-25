(** Federer (1969), 3.3.4, pp. 289–290:
    measurability of the original exceptional
    set and its continuous coset preimage.
    The accumulation locus remains Suslin;
    no Borel hull replaces the original D. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureFiniteClosure BorelRegularMeasureUP
  TopologicalBorel ContinuousBorelPreimages SuslinSetUP SuslinPreimages SuslinMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_exceptional_preimage_measurable]:
    the measurable exceptional set used in
    the Haar/Fubini argument of Federer
    3.3.4, pp. 289–290. Original B_j
    and C_j are Borel and D is
    Suslin. Under a continuous coset map,
    these exact preimages are measurable
    for the actual Borel-regular source
    measure by 2.2.12, p. 68. *)
Theorem structure_exceptional_preimage_measurable (R:realType)
    (P Q:topologicalType) (mu:set Q->\bar R) (F:Q->P) (B C D:set P):
  is_measure mu ->is_borel_regular_measure mu ->continuous F ->
  borel_set B ->borel_set C ->is_suslin_set R D ->
  measure_measurable mu (F @^-1` (~` (B `|` C `|` D))).
Proof.
move=>hMu hRegular hF hB hC hD.
have hPB:=borel_regular_borel_measurable hMu hRegular (continuous_borel_preimage hF hB).
have hPC:=borel_regular_borel_measurable hMu hRegular (continuous_borel_preimage hF hC).
have hClosed S:closed S ->measure_measurable mu S.
  move=>hS; exact:(borel_regular_borel_measurable hMu hRegular (closed_borel_set hS)).
have hPD:=suslin_set_measurable hMu hClosed (continuous_preimage_suslin hF hD).
rewrite -preimage_setC !preimage_setU.
apply:measure_measurable_complement.
exact:(@measure_measurable_union R Q mu hMu _ _
  (@measure_measurable_union R Q mu hMu _ _ hPB hPC) hPD).
Qed.
