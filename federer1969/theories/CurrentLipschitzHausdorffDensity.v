(** Federer (1969), 4.1.25, p. 383: identify
    the actual sealed Hausdorff-density current with
    the original sealed Lipschitz image. Derive the
    density module's original local-integrability inputs
    from the proved target L1 field; no ambient
    Radon or current-representation premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness InnerOwnNormTopology ExteriorGrading
  CurrentSpaces CurrentDensityUP CurrentDensitySealed CurrentDensityUniqueness
  CurrentCoefficientNorms CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient LipschitzUP LipschitzBasic
  CurrentFlatLipschitzPushforwardSealed CurrentLipschitzLebesgueActionDensity
  CurrentAreaNormalisedImageSealed CurrentAreaFibreDensitySealed
  CurrentAreaFibreDensityMeasurable CurrentAreaFibreDensitySummable
  CurrentLipschitzHausdorffAction CurrentSummableDensityLocal
  HausdorffMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP TopologicalBorel
  PartialFunctionUP PartialFunctionExtensionUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_hausdorff_measure_open_measurable]:
    actual H^m meets the original measurable-open-set
    input of the density current used in Federer
    4.1.25, p. 383. This uses Borel regularity
    from 2.10.2, p. 170; local finiteness on
    the entire target space is unnecessary. *)
Lemma current_area_hausdorff_measure_open_measurable (R : realType) n m :
  @is_current_density_borel_measure R n
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m).
Proof.
move=> A hOpen.
apply: (borel_regular_borel_measurable
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
  (@hausdorff_measure_borel_regular R (inner_metric_space (@euclidean_inner_productP R n)) m)).
exact: (inner_own_norm_borel_iff (@euclidean_inner_productP R n) A).2
  (open_borel_set hOpen).
Qed.

Section ActualHausdorffDensity.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation FullX := (fun _ : X => True).
Local Notation FullY := (fun _ : Y => True).
Local Notation hFullX := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation hFullY := (fun (y : Y) (_ : True) => norm_full_domain_interior NY y).
Variable xi : @compact_summable_multivector_space R h2 m m FullX hFullX.
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 m m FullX hFullX xi).
Local Notation T := (@compact_summable_multivector_current R h2 m m FullX hFullX xi).
Local Notation hFlat := (@current_lipschitz_lebesgue_action_density_flat R h2 m m FullX hFullX xi).
Variable f : X -> Y.
Hypothesis hLip : @is_metric_lipschitz R
  (inner_metric_space (@euclidean_inner_productP R m))
  (inner_metric_space (@euclidean_inner_productP R n)) setT f.
Local Notation hLocal := (@metric_lipschitz_is_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) setT f hLip).
Local Notation hImage := (fun (x : X) (_ : True) => Logic.I).
Local Notation Q := (@CurrentFlatLipschitzPushforward.value R h2 m n m
  FullX FullY hFullX hFullY f hImage hLocal T hFlat).
Local Notation H := (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m).
Local Notation hH := (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m).
Local Notation hBorel := (@current_area_hausdorff_measure_open_measurable R n m).
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f raw).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X n m f u).

(** Source for [current_lipschitz_hausdorff_density]: the
    second original displayed identity of Federer
    4.1.25, p. 383, for the actual opaque
    Lipschitz image and actual opaque density current.
    Every local input of the density construction
    is proved from the original compact summable
    field and Lipschitz map. *)
Theorem current_lipschitz_hausdorff_density
    (w : Y -> exterior_power Y m) :
  is_partial_function_total_extension eta w ->
  exists hField : @is_locally_integrable_current_density R h2 n m H w,
    Q = @CurrentDensity.value R h2 n m H hH hBorel w hField.
Proof.
move=> hW; have [L [hL hBound]] := hLip.
have [b [hIntegral _]] := @current_area_fibre_representative_norm_integral
  R h2 m n xi f hLip w L hW hL hBound.
have hMeas := @current_area_fibre_representative_measurable R h2 m n xi f hLip w hW.
have hField := @current_summable_density_locally_integrable R h2 n m
  H hH hBorel w b hMeas hIntegral.
exists hField.
exact: (@current_density_action_unique R h2 n m H w Q
  (@CurrentDensity.value R h2 n m H hH hBorel w hField)
  (@current_lipschitz_hausdorff_action R h2 m n xi f hLip w hW)
  (@CurrentDensity.laws R h2 n m H hH hBorel w hField)).
Qed.
End ActualHausdorffDensity.
