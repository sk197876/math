(** Federer (1969), 4.1.26, p. 383:
    at Lebesgue almost every target point,
    the original degree is the finite
    numerical sum of the actual determinant
    signs over A intersected with the fibre.
    This statement retains the exact partial
    differential and signed-summation domains. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm InnerMetric
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  EuclideanLebesgueDimensions MetricDiameter LipschitzUP
  PartialFunctionUP NumericalSum MeasureUP MeasureAlmostUP MeasureAlmostBasic
  LipschitzDegreeSealed LipschitzDegreeFibreGraph LipschitzDegreeCharacteristicImage
  CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_degree_almost_fibre_formula]:
    the complete original almost-everywhere displayed
    formula of 4.1.26, p. 383. A
    bounded Lebesgue-measurable A and global Lipschitz
    f are the only analytic inputs. *)
Theorem lipschitz_degree_almost_fibre_formula (R:realType)
    (h2:(1+1:R)!=0) m (f:R_n R m->R_n R m)
    (hLip:@is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R m)) setT f)
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A):
  measure_almost_everywhere (@euclidean_lebesgue_measure R m) [set y|
    exists a:R,partial_function_graph (@LipschitzDegree.value R m f A) y a /\
    exists w:R_n R m->R,
      (forall x,A x->f x=y->exists D:Hom (R_n R m) (R_n R m),
        has_norm_differential (inner_norm (@euclidean_inner_productP R m))
          (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) f x D /\
        Num.sg (@euclidean_det R m (hom_as_linear D))=w x) /\
      numerical_sum (A `&` [set x|f x=y]) (fun x=>(w x)%:E)=Some a%:E].
Proof.
apply:(@measure_almost_everywhere_mono R (R_n R m) (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) _ _ _
  (@lipschitz_degree_conull_domain R h2 m f hLip A hA hBound))=>y [a ha].
exists a;split;first exact:ha.
exact:(@lipschitz_degree_fibre_graph R m f A y a).1 ha.
Qed.
