(** Federer (1969), 4.1.8, p. 361: measurability
    of the original product-density coefficient on the
    actual Euclidean product domain. Reuse the original
    product-measure cylinders, finite bilinear continuity
    and the genuine coordinate measure bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations ExteriorGrading
  EuclideanCartesianMap CurrentDomain CurrentCoefficientNorms CurrentMultivectorDual
  CurrentMeasurableProductCoefficients CurrentDensityNormMeasurable
  CurrentCartesianVectorProduct CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon MeasureBijectionIntegralTransport
  OpenFamilyTopologyMathcomp PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP ProductMeasure MeasurableFunctionUP ProductFunctionMeasurability
  MeasurableBoundedBilinearProduct MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianDensityMeasurable.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) (@euclidean_cartesian_set R m n A B)).
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Local Notation VA := (exterior_power (R_n R m) i).
Local Notation VB := (exterior_power (R_n R n) j).
Local Notation VC := (exterior_power (R_n R (m+n)) (i+j)).
Local Notation hNA := (@current_vector_mass_real_norm R h2 m i).
Local Notation hNB := (@current_vector_mass_real_norm R h2 n j).
Local Notation hNC := (@current_vector_mass_real_norm R h2 (m+n) (i+j)).
Local Notation WA := (open_family_topological_space (@current_multivector_weak_laws R m i).1).
Local Notation WB := (open_family_topological_space (@current_multivector_weak_laws R n j).1).
Local Notation WC := (open_family_topological_space (@current_multivector_weak_laws R (m+n) (i+j)).1).
Local Notation F := (@current_cartesian_vector_product R m n i j).
Variables (xi:AT->VA) (eta:BT->VB).

(** Source for [current_cartesian_density]: the original
    included wedge coefficient at the original two
    coordinates, supporting Federer 4.1.8, p. 361. *)
Definition current_cartesian_density (z:CT):VC:=F (xi (D z).1) (eta (D z).2).

(** Source for [current_cartesian_density_join]: the original
    product-density formula at a joined pair, supporting
    Federer 4.1.8, p. 361. *)
Lemma current_cartesian_density_join (z:AT*BT):
  current_cartesian_density (J z)=F (xi z.1) (eta z.2).
Proof. by rewrite /current_cartesian_density current_cartesian_domain_join_split. Qed.

Variables (alpha:set AT->\bar R) (beta:set BT->\bar R).
Hypothesis hAlpha:is_measure alpha.
Hypothesis hBeta:is_measure beta.
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Hypothesis hXi:is_measure_measurable_function alpha (partial_function_total (fun x=>(xi x:WA))).
Hypothesis hEta:is_measure_measurable_function beta (partial_function_total (fun x=>(eta x:WB))).

(** Source for [current_cartesian_pair_density_measurable]:
    the original exterior product of the two measurable
    density fields is mass-norm measurable for the original
    product measure, supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_pair_density_measurable:
  is_measure_measurable_function mu (partial_function_total
    (fun z:AT*BT=>(F (xi z.1) (eta z.2):real_norm_metric_space hNC))).
Proof.
have hX:=@current_density_mass_topology_measurable R h2 m i AT alpha hAlpha xi hXi.
have hY:=@current_density_mass_topology_measurable R h2 n j BT beta hBeta eta hEta.
have hFirst:=@product_measurable_first_function R AT BT (real_norm_metric_space hNA)
  alpha beta hAlpha hBeta (fun x=>(xi x:real_norm_metric_space hNA)) hX.
have hSecond:=@product_measurable_second_function R AT BT (real_norm_metric_space hNB)
  alpha beta hAlpha hBeta (fun x=>(eta x:real_norm_metric_space hNB)) hY.
exact:(@measurable_bounded_bilinear_product R (Choice.clone (AT*BT)%type _)
  VA VB VC (@current_vector_mass R h2 m i) (@current_vector_mass R h2 n j)
  (@current_vector_mass R h2 (m+n) (i+j)) hNA hNB hNC mu hm F
  (@current_cartesian_vector_product_bounded R h2 m n i j)
  (fun z=>xi z.1) (fun z=>eta z.2)
  (@current_vector_coefficient_separable R h2 m i)
  (@current_vector_coefficient_separable R h2 n j) hFirst hSecond).
Qed.

(** Source for [current_cartesian_density_norm_measurable]: the
    original product density is mass-norm measurable on
    the actual Euclidean product domain, supporting Federer
    4.1.8, p. 361. Completed measurability is transported
    through the actual measure bijection. *)
Theorem current_cartesian_density_norm_measurable:
  is_measure_measurable_function lambda (partial_function_total
    (fun z=>(current_cartesian_density z:real_norm_metric_space hNC))).
Proof.
apply:(@measure_bijection_measurable_iff R (Choice.clone (AT*BT)%type _) CT
  mu lambda J D (@current_cartesian_measure_bijection R m n A B alpha beta hAlpha hBeta)
  (real_norm_metric_space hNC) _).1.
apply:(@measurable_function_graph_equivalent R (Choice.clone (AT*BT)%type _)
  (real_norm_metric_space hNC) mu _ _ _ current_cartesian_pair_density_measurable)=>z v.
change (F (xi z.1) (eta z.2)=v <->current_cartesian_density (J z)=v).
by rewrite current_cartesian_density_join.
Qed.

(** Source for [current_cartesian_density_weak_measurable]:
    the original weak product-density field is measurable,
    supporting the Radon representation in Federer 4.1.8,
    p. 361. Both zero degrees are included. *)
Theorem current_cartesian_density_weak_measurable:
  is_measure_measurable_function lambda (partial_function_total
    (fun z=>(current_cartesian_density z:WC))).
Proof.
exact:(@current_density_weak_topology_measurable R h2 (m+n) (i+j) CT lambda
  (@current_cartesian_measure_is_measure R m n A B alpha beta hAlpha hBeta)
  current_cartesian_density current_cartesian_density_norm_measurable).
Qed.
End CurrentCartesianDensityMeasurable.
