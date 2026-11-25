(** Federer (1969), 4.1.7, p. 355: the four
    original spaces E^m, E_m, D^m and D_m. They are
    the actual opaque smooth and distribution spaces
    from 4.1.1 with real covector target and comass
    norm. No new construction of a dual is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  AlternatingForms CurrentCoefficientNorms Distributions
  ContinuousRealDual SmoothFunctionTopology SmoothDualRestriction
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces
  SmoothTestTopology FunctionalSupportUP SmoothFunctionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSpaces.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation NY := (fun m=>@current_form_comass R h2 n m).
Local Notation hNY := (fun m=>@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.

(** Source for [current_smooth_space]: E^m(U)=E(U,A^m R^n),
    Federer 4.1.7, p. 355. *)
Definition current_smooth_space m:lmodType R:=
  @distribution_smooth_space R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_smooth_value]: actual form values
    in the original E^m(U), Federer 4.1.7, p. 355. *)
Definition current_smooth_value m:current_smooth_space m->X->Y m:=
  @distribution_smooth_value R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_smooth_space_laws]: E^m(U)
    consists of exactly the original smooth real forms,
    Federer 4.1.7, p. 355. *)
Definition current_smooth_space_laws m:
    is_smooth_function_space hNX (hNY m) U (@current_smooth_value m):=
  @distribution_smooth_laws R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_smooth_derivatives]: original
    higher derivatives of E^m(U), inherited from
    4.1.1, pp. 343–344, in Federer 4.1.7, p. 355. *)
Definition current_smooth_derivatives m:=
  @distribution_smooth_derivatives R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_smooth_derivative_laws]: the
    actual derivative specification for the original
    smooth forms, Federer 4.1.7, p. 355. *)
Definition current_smooth_derivative_laws m:
    @is_smooth_function_derivatives R X (Y m) NX (NY m) hNX (hNY m) U
      (current_smooth_space m) (@current_smooth_value m) (@current_smooth_derivatives m):=
  @distribution_smooth_derivative_laws R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_test_space]: D^m(U)=D(U,A^m R^n),
    compactly supported original smooth forms,
    Federer 4.1.7, p. 355. *)
Definition current_test_space m:lmodType R:=
  @distribution_test_space R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_test_value]: evaluation of the
    original test forms, Federer 4.1.7, p. 355. *)
Definition current_test_value m:current_test_space m->X->Y m:=
  @distribution_test_value R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_test_opens]: the original final
    topology on D^m(U), inherited from 4.1.1, p. 344,
    in Federer 4.1.7, p. 355. This does not identify
    it with the locally convex inductive topology. *)
Definition current_test_opens m:=
  @distribution_test_opens R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_space]: D_m(U)=D'(U,A^m R^n),
    the original m-dimensional currents,
    Federer 4.1.7, p. 355. *)
Definition current_space m:lmodType R:=
  @distribution_space R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_value]: T(phi), the actual
    continuous-dual action of a current on a test
    form, Federer 4.1.7, p. 355. *)
Definition current_value m:Hom (current_space m) (Hom (current_test_space m) R^o):=
  @distribution_value R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_weak_opens]: the original weak
    current topology inherited from 4.1.1, p. 345,
    in Federer 4.1.7, p. 355. *)
Definition current_weak_opens m:=
  @distribution_weak_opens R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_support]: the original support
    of T, specified by local annihilation in 4.1.1,
    p. 345, as used in Federer 4.1.7, pp. 355–359. *)
Definition current_support m (T:current_space m):set X:=
  @smooth_functional_support R X (Y m) NX hNX U
    (current_test_space m) (@current_test_value m) (@current_value m T).

(** Source for [current_smooth_dual_space]: E_m(U)=
    E'(U,A^m R^n), Federer 4.1.7, p. 355. Its
    compact-support image is proved separately through
    the original restriction map of 4.1.1. *)
Definition current_smooth_dual_space m:lmodType R:=
  @continuous_real_dual_space R (current_smooth_space m)
    (smooth_function_opens (current_smooth_derivative_laws m))
    (smooth_function_topology_laws (current_smooth_derivative_laws m)).1.

(** Source for [current_smooth_dual_restriction]: the
    original E_m(U) to D_m(U) map, Federer 4.1.7,
    p. 355, obtained by restricting to actual tests. *)
Definition current_smooth_dual_restriction m:
    Hom (current_smooth_dual_space m) (current_space m):=
  @smooth_dual_test_restriction R X (Y m) NX (NY m) hNX (hNY m) U
    (current_smooth_space m) (@current_smooth_value m) (current_smooth_space_laws m)
    (@current_smooth_derivatives m) (current_smooth_derivative_laws m).
End CurrentSpaces.
