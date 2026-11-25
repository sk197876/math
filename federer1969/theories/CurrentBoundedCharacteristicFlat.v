(** Federer (1969), 4.1.26, pp. 383–384:
    a bounded measurable source set supplies the
    original compact flat Euclidean restriction. This
    is the compact summable field from the
    proof's substitution into 4.1.25, without any
    normality or finite-perimeter premise. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDensityUP FlatCurrentsUP MetricDiameter
  CompactSummableMultivectors CompactSummableMultivectorDensity
  EuclideanCharacteristicCurrent EuclideanLebesgueDimensions MeasureUP
  CurrentLipschitzLebesgueActionDensity CurrentBoundedCharacteristicCurrent
  CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_bounded_characteristic_flat]:
    E^m restricted to bounded measurable A
    belongs to the original compact-flat union,
    supporting the actual image in 4.1.26,
    p. 383. Existence follows from the
    already proved compact summable representative. *)
Theorem current_bounded_characteristic_flat (R:realType)
    (h2:(1+1:R)!=0) m (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A):
  @is_flat_current R h2 m m (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) x)
    (@euclidean_characteristic_current R h2 m A hA).
Proof.
have[xi [_ [hCurrent _]]]:=@current_bounded_characteristic_current_exists
  R h2 m A hA hBound.
rewrite -hCurrent.
exact:(@current_lipschitz_lebesgue_action_density_flat R h2 m m
  (fun _=>True) (fun x (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R m)) x) xi).
Qed.
