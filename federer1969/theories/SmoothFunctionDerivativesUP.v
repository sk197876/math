(** Federer (1969), 4.1.1, pp. 343–344: the actual higher
    derivatives used in nu^i_K. The operators are linear in the
    smooth function and continuous in the base point. Their values
    belong to the existing opaque multilinear spaces of 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormClassOneUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothDerivativeSpecification.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable value:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ev := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).

(** Source for [is_smooth_function_derivatives]: independent
    specification of the derivative operators on E(U,Y), Federer
    4.1.1, pp. 343–344. Linearity is carried by the Hom types;
    existence and the analytic properties must be proved separately. *)
Record is_smooth_function_derivatives (D:forall k,X->Hom E (Z k)) : Prop := {
  (** Source for [smooth_derivative_exact]: the operators give the
      original recursive higher differentials of the function on U,
      Federer 4.1.1, p. 343, using 3.1.11, pp. 218–220. *)
  smooth_derivative_exact : forall k f x,U x ->
    has_norm_higher_differential NX ev ZN U (value f) k x (D k x f);
  (** Source for [smooth_derivative_continuous]: every higher
      derivative of a smooth function is continuous on U, supporting
      the compact-set seminorms of Federer 4.1.1, p. 343. *)
  smooth_derivative_continuous : forall k f,
    norm_class_zero NX (@ZN k) U (fun x=>D k x f);
  (** Source for [smooth_derivative_outside]: zero values outside
      U normalize total representatives; the higher differential
      itself retains its actual domain, Federer 4.1.1, p. 343. *)
  smooth_derivative_outside : forall k f x,~U x -> D k x f=0
}.
End SmoothDerivativeSpecification.
