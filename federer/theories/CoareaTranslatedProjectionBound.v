(** Federer (1969), 3.2.11, p. 249: identify
    each section of the translated integrand with the actual
    double fibre, then apply the unit projection estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBlockLinearMaps CoareaPerturbationMap CoareaCylinderFibres CoareaSliceHausdorff
  CoareaTranslatedCutoff CoareaProjectionFibreBound MappingMultiplicity HausdorffMeasure HausdorffFibreCost
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialZeroExtension PartialProductSections
  MeasureIntegralBounds MeasureBoundGraphEquivalence ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_translated_projection_bound]: the
    application of 2.10.25 to p in Federer 3.2.11,
    p. 249. The fibre degree is exactly m-n,
    and the perturbed fibre has Hausdorff degree m;
    no measurability or finiteness of that fibre is needed. *)
Theorem coarea_translated_projection_bound (R:realType) m n
    (f:R_n R m->R_n R n) (e:R) A B y:
  (n<=m)%N ->
  measure_upper_integral (@euclidean_lebesgue_measure R n)
    (partial_product_vertical_section
      (coarea_translated_cutoff
        (fun y=>(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m))
          (m-n) (mapping_fibre f A y):extended_real_line R)) e B) y)<=
  (hausdorff_fibre_bound_constant (m-n) n (1:R))%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) m
      (mapping_fibre (coarea_perturbation_map f e) (coarea_cylinder A B) y).
Proof.
move=>hnm.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose P:=inner_metric_space (@euclidean_inner_productP R (m+n)).
pose S:=mapping_fibre (coarea_perturbation_map f e) (coarea_cylinder A B) y.
pose theta:=fun y=>(@hausdorff_measure R X (m-n) (mapping_fibre f A y):extended_real_line R).
pose F:=partial_product_vertical_section (coarea_translated_cutoff theta e B) y.
pose v:=fun z=>(@hausdorff_measure R P (m-n)
  (mapping_fibre (@euclidean_last_block R m n) S z):extended_real_line R).
have hEq:measure_upper_integral (@euclidean_lebesgue_measure R n) F=
    measure_upper_integral (@euclidean_lebesgue_measure R n) (partial_function_total v).
  apply:measure_upper_integral_graph_equivalent=>z t.
  change (partial_function_graph (coarea_translated_cutoff theta e B) (y,z) t <->v z=t).
  case:(pselect (B z))=>hz.
  - rewrite /coarea_translated_cutoff partial_function_zero_extension_on //.
    rewrite /v (coarea_double_fibre_mass_inside (m-n) f e A y hz).
    by [].
  - rewrite /coarea_translated_cutoff partial_function_zero_extension_off; last by move=>[_ h]; exact:hz h.
    rewrite /v (coarea_double_fibre_mass_outside (m-n) f e A y hz).
    by split=>h; symmetry.
rewrite hEq.
have hBound:=@coarea_projection_fibre_upper_bound R m n (m-n) S.
have hDegree:=congr1 (fun d:nat=>@hausdorff_measure R P d S) (subnK hnm).
by rewrite hDegree in hBound.
Qed.
