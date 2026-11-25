(** Federer (1969), 4.1.7, p. 356: the
    original local integrability conditions for a
    current density on R^n. These are mathematical
    input properties, independent of constructing a current. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  CurrentCoefficientNorms CurrentSpaces CurrentMultivectorDual MultivectorDualSealed
  MeasureUP DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDensityInputs.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).

(** Source for [full_current_space]: actual currents
    on the whole original R^n, supporting Federer
    4.1.7, p. 356. This is an alias of
    the original continuous-dual space. *)
Definition full_current_space:lmodType R:=
  @current_space R h2 n (fun _=>True) hFull m.

(** Source for [is_current_density_borel_measure]:
    measurability of original open sets, supporting
    the integral construction of Federer 4.1.7,
    p. 356. Radon measures satisfy this condition. *)
Definition is_current_density_borel_measure (gamma:set X->\bar R):Prop:=
  forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable gamma A.

(** Source for [is_locally_integrable_current_density]:
    original weak measurability and finite compact
    mass integrals, supporting Federer 4.1.7,
    p. 356, through 4.1.1, p. 346. *)
Definition is_locally_integrable_current_density (gamma:set X->\bar R) (xi:X->exterior_power X m):Prop:=
  @is_locally_integrable_weak_dual_field R X (A_m X R^o m) NX hNX (exterior_power X m)
    (@MultivectorDual.evaluation R X m) (@current_vector_mass R h2 n m)
    (@current_multivector_weak_opens R n m) (@current_multivector_weak_laws R n m) gamma xi.
End CurrentDensityInputs.
