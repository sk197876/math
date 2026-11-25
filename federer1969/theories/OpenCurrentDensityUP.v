(** Federer (1969), 4.1.7, pp. 355–358: the
    original local mass-integrability conditions on
    an arbitrary open U, independent of constructing
    the represented current. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentCoefficientNorms CurrentMultivectorDual
  OpenFamilyTopologyMathcomp PartialFunctionBasic MeasurableFunctionUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OpenCurrentDensityInput.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Local Notation UT := (set_type (U:set XT)).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hWeak := (@current_multivector_weak_laws R n m).

(** Source for [is_locally_integrable_open_current_density]:
    original weak measurability and finite mass
    integrals on every compact subset of U,
    supporting Federer 4.1.7, pp. 356–358.
    The measure's Radon laws are separate inputs. *)
Definition is_locally_integrable_open_current_density (gamma:set UT->\bar R) (xi:UT->V):Prop:=
  is_measure_measurable_function gamma
    (partial_function_total (fun x=>(xi x:open_family_topological_space hWeak.1))) /\
  forall K:set UT,compact K->exists c:R,
    is_measure_subset_integral gamma K (real_total_integrand (fun x=>VN (xi x))) c%:E.
End OpenCurrentDensityInput.
