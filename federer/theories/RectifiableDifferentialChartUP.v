(** Federer (1969), 3.2.19, p. 256: laws for a chart point
    where the actual differential identifies the approximate tangent and
    the partial approximate differential obeys the printed chain rule.
    Existence is proved separately from these laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialFunctionPrecomposition MeasureRestriction HausdorffMeasure
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_rectifiable_differential_chart_point]: the two
    tangent-plane and approximate-differential displays in the proof of
    Federer 3.2.19, p. 256. Both source differentials are actual
    differentials, and the approximate differential retains exactly its
    tangent-plane domain. The existential data are not extra hypotheses
    in the final rectifiable-set theorem. *)
Definition is_rectifiable_differential_chart_point (R : realType) m n k
    (W : set (R_n R n)) (K : set (R_n R m))
    (psi : R_n R m -> R_n R n) (F : R_n R n -> R_n R k) w : Prop :=
  exists a (D : Hom (R_n R m) (R_n R n))
    (H : Hom (R_n R m) (R_n R k)) (d : partial_function (R_n R n) (R_n R k)),
    K a /\ psi a=w /\ injective D /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H /\
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) W) m w=range D /\
    is_measure_approximate_differential (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict (@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) m) W) m
      (partial_function_source_restrict W (partial_function_total F)) w d /\
    partial_function_precompose D d=partial_function_total H.
