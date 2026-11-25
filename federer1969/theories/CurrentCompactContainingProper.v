(** Federer (1969), 4.1.9, p. 363: a smooth homotopy
    is proper on the closed time cylinder of a compactly
    supported current. This supporting general restriction
    lemma reuses original class-zero continuity and the
    compact-source proper-map theorem; no global properness
    of the map on its open source is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormClassZeroTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentDomain
  CurrentProperOnContainingSet ProperMapUP CompactPushforwardSupport IsotropyGroupTopology SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CurrentCompactContainingProper.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U:set X) (V:set Y) (C:set X).
Hypothesis hCU:C `<=` U.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hF:norm_class_zero NX NY U f.
Local Notation CT := [the topologicalType of set_type (C:set XT)].
Local Notation UT := (current_domain R n U).
Local Notation VT := (current_domain R nu V).
Local Notation mapC := (@current_map_on_containing_set R n nu U V C hCU f hImage).

(** Source for [current_containing_map_continuous]: the actual
    restriction to the original specified subset is continuous,
    supporting the cylinder properness in Federer 4.1.9,
    p. 363. Only continuity on the original U is used. *)
Theorem current_containing_map_continuous:continuous mapC.
Proof.
pose inclusion:CT->UT:=fun x=>exist _ (set_val x) (mem_set (@hCU _ (set_valP x))).
have hInclusion:continuous inclusion.
  apply:(@set_type_continuous_into XT U CT inclusion).
  exact:(@set_type_val_continuous XT C).
have hOriginal:=@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U f hF.
apply:(@set_type_continuous_into YT V CT mapC).
move=>x;exact:(@continuous_comp CT [the topologicalType of UT] [the topologicalType of YT]
  inclusion (fun y:UT=>(f (set_val y):YT)) x (hInclusion x) (hOriginal (inclusion x))).
Qed.

(** Source for [current_compact_containing_map_proper]: a
    continuous map on a compact original restriction is
    proper into the original Hausdorff target domain,
    supporting Federer 4.1.9, p. 363. *)
Theorem current_compact_containing_map_proper:
  @compact XT C->is_proper_map mapC.
Proof.
move=>hCompact.
have hPre:=@set_type_compact_preimage XT C C hCompact (fun x hx=>hx).
have hEqual:(set_val @^-1` C:set CT)=setT.
  apply/seteqP;split;first by [].
  move=>x _;exact:set_valP x.
have hWhole:@compact CT setT by rewrite -hEqual.
exact:(@compact_source_continuous_map_proper CT VT mapC hWhole
  (@set_type_hausdorff YT V (@metric_hausdorff R YT)) current_containing_map_continuous).
Qed.
End CurrentCompactContainingProper.
