(** Federer (1969), 3.3.4, p. 291: apply
    2.9.17 outside the original Suslin support
    image R_v. Keep the actual reference and
    arbitrary numerator outer measure, with no
    source hull or numerator regularity premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import StructureProjectiveSpace StructureProjectiveMeasure
  StructureProjectiveDerivation MeasureUP MeasureSplit MeasureFiniteClosure MeasureAlmostUP
  MeasureDerivationContext BorelRegularMeasureUP TopologicalBorel
  SuslinSetUP SuslinMeasurability UpperBallRatioDichotomy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_original_support_dichotomy]:
    the null exceptional reference set outside
    the original R_v in Federer 3.3.4, p. 291,
    before comparison with the unnormalized t^(-m)
    values. Closed-ball upper ratios are zero
    or infinite almost everywhere outside that
    original image, for any numerator outer measure. *)
Theorem structure_projective_original_support_dichotomy (R:realType) m
    (psi:set (structure_projective_space R m)->\bar R)
    (S:set (structure_projective_space R m)):
  is_measure psi ->is_suslin_set R S ->psi (~` S)=0%E ->
  measure_almost_everywhere (@structure_projective_measure R m)
    (S `|` has_zero_or_infinite_upper_ball_ratio psi (@structure_projective_measure R m)).
Proof.
move=>hPsi hS hNull.
have hRef:=@structure_projective_derivation_measure R m.
have hMu:=derivation_measure_law hRef.
have hClosed C:closed C ->measure_measurable (@structure_projective_measure R m) C.
  move=>hC; exact:(borel_regular_borel_measurable hMu
    (derivation_measure_borel_regular hRef) (closed_borel_set hC)).
have hMeas:=suslin_set_measurable hMu hClosed hS.
have hComp:=measure_measurable_complement hMeas.
have hAlmost:=structure_projective_ratio_dichotomy hPsi hComp hNull.
by rewrite /measure_almost_everywhere setCU; exact:hAlmost.
Qed.
