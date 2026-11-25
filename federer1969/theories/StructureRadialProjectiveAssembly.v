(** Federer (1969), 3.3.4, p. 291:
    apply the actual projective open-ball dichotomy
    to each original radial image measure and
    assemble all positive reciprocal cutoffs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import StructureProjectiveSpace StructureProjectiveMeasure
  StructureRadialProjectiveAlternatives StructureRadialImageMeasure StructureRadialImageLaws
  StructureRadialImageSuslin StructureProjectiveOpenBallDichotomy StructureCountableNullAlternatives
  MeasureDerivationContext MeasureUP MeasureAlmostUP MeasureAlmostBasic
  SuslinSetUP CompleteMetricUP BorelFunctionUP TopologicalBorel
  CompactCauchyLimits CompactMetricSeparability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_radial_projective_assembled_alternatives]:
    H^m[T(U) minus (P union Q union R)]=0,
    Federer 3.3.4, p. 291, for the actual
    radial numerator measures and original images.
    Actual Suslin-image and outer-measure proofs
    discharge every per-cutoff premise; the
    decreasing infinite and image alternatives
    justify the countable assembly. *)
Theorem structure_radial_projective_assembled_alternatives (R:realType) (X:metricType R)
    m (phi:set X->\bar R) (A D:set X) (a:X)
    (f:X->structure_projective_space R m):
  is_measure phi ->is_complete_metric_space X ->
  (exists C:set X,countable C /\ dense C) ->
  is_suslin_set R A ->borel_set D ->is_borel_function f ->
  @structure_projective_measure R m
    (setT `\` ((\bigcup_v @structure_radial_projective_zero R X m phi A D a f v) `|`
      (\bigcap_v @structure_radial_projective_infinite R X m phi A D a f v) `|`
      (\bigcap_v @structure_radial_projective_image R X m A D a f v)))=0%E.
Proof.
move=>hPhi hX hSX hA hD hF.
have hMu:=derivation_measure_law (@structure_projective_derivation_measure R m).
apply:structure_countable_alternatives_null=>//.
- exact:structure_radial_projective_infinite_decreases.
- exact:structure_radial_projective_image_decreases.
- move=>v.
  have hPositive:0<((v.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
  have hPsi:=structure_radial_image_is_measure m A a D f hPhi hPositive.
  have hComp:=compact_metric_space_complete (@structure_projective_space_compact R m).
  have hSep:=compact_metric_countable_dense_set (@structure_projective_space_compact R m).
  have hImage:=structure_radial_original_image_suslin a ((v.+1)%:R:R)^-1
    hX hComp hSX hSep hA hD hF.
  have hNull:=structure_radial_image_original_support_null m A a D f hPhi hPositive.
  have hAlmost:=structure_projective_open_ball_dichotomy hPsi hImage hNull.
  apply:(measure_null_subset hMu _ hAlmost)=>z [_ hBad] hGood; apply:hBad.
  case:hGood=>[hImageZ|[hZero|hInfinite]].
  + by right.
  + by left; left.
  + by left; right.
Qed.
