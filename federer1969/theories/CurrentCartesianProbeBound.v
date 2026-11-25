(** Federer (1969), 4.1.8, p. 360: the fixed-cutoff
    first-current action has one finite derivative-seminorm bound
    on the whole smooth product space. This supporting bound uses
    the exact smooth-dual criterion of 4.1.1, p. 344.
    The bound is uniform in the smooth input; all operators are
    actual proved smooth interior, pullback and cutoff maps. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockLinearMaps ExteriorGrading ExteriorMaps
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces
  SmoothConstantSealed SmoothCurrentVectorInterior SmoothFormPullbackSealed
  SmoothFormPullbackContinuity SmoothCompactSet SmoothCutoffReplacement
  SmoothTestSpaces SmoothTestTopology SmoothFunctionTopology
  OpenFamilyTopologyUP NormOpenTopology ContinuousRealDual SmoothDualFiniteBound CurrentCartesianProbe.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianProbeBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variable A:set X.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Local Notation Full := (fun _:Z=>True).
Local Notation hFull := (fun z (_:True)=>norm_full_domain_interior NZ z).
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation EA := (@current_smooth_space R h2 m A hA i).
Local Notation va := (@current_smooth_value R h2 m A hA i).
Local Notation hEA := (@current_smooth_space_laws R h2 m A hA i).
Local Notation DA := (@current_test_space R h2 m A hA i).
Local Notation D := (fun k=>@current_test_space R h2 (m+n) Full hFull k).
Local Notation E := (fun k=>@current_smooth_space R h2 (m+n) Full hFull k).
Local Notation hE := (fun k=>@current_smooth_space_laws R h2 (m+n) Full hFull k).
Local Notation V := (@current_vector_smooth_space R h2 (m+n) Full hFull j).
Local Notation vv := (@current_vector_smooth_value R h2 (m+n) Full hFull j).
Local Notation hV := (@current_vector_smooth_space_laws R h2 (m+n) Full hFull j).
Local Notation VN := (@current_vector_mass R h2 (m+n) j).
Local Notation hVN := (@current_vector_mass_real_norm R h2 (m+n) j).
Local Notation C0 := (@SmoothConstant.operator R Z (exterior_power Z j) NZ VN hNZ hVN
  Full hFull V vv hV).
Local Notation M := (@smooth_current_vector_interior R h2 (m+n) j i Full hFull).

Local Notation hImage := (fun a (_:A a)=>I).
Local Notation Pull := (@SmoothFormPullback.operator R h2 m (m+n) i A Full hA hFull P
  hImage (@current_cartesian_first_injection_smooth R m n A hA)).
Variable K:smooth_compact_set hNX A.
Local Notation C := (@smooth_cutoff_replacement R X (A_m X R^o i) NX
  (@current_form_comass R h2 m i) hNX (@current_form_comass_real_norm R h2 m i)
  m (@coordinate_basis R m) (@coordinate_basisP R m) A hA EA va hEA K).

(** Source for [current_cartesian_probe_smooth_bound]: one
    finite order, compact index and scalar constant control
    every smooth input in the original fixed-cutoff first-current
    action, supporting Federer 4.1.8, p. 360. The
    first current and exterior vector are arbitrary. *)
Theorem current_cartesian_probe_smooth_bound
    (S:@current_space R h2 m A hA i) (eta:exterior_power Y j):
  exists r:nat,exists J:smooth_compact_set hNZ Full,exists M0:R,0<=M0 /\
    forall psi:E (j+i),
      `|@current_value R h2 m A hA i S
        (C (Pull (M (C0 (exterior_power_map (hom_as_linear Q) j eta)) psi)))|<=
      M0*smooth_function_derivative_seminorm
        (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)) J r psi.
Proof.
pose xi:=C0 (exterior_power_map (hom_as_linear Q) j eta).
pose L:=hom_comp (@current_value R h2 m A hA i S) (hom_comp C (hom_comp Pull (M xi))).
have hM:=@smooth_current_vector_interior_continuous R h2 (m+n) j i Full hFull xi.
have hPull:=@smooth_form_pullback_continuous R h2 m (m+n) i A Full hA hFull P
  hImage (@current_cartesian_first_injection_smooth R m n A hA) Pull
  (@SmoothFormPullback.laws R h2 m (m+n) i A Full hA hFull P hImage
    (@current_cartesian_first_injection_smooth R m n A hA)).
have hC:=@smooth_cutoff_replacement_continuous R X (A_m X R^o i) NX
  (@current_form_comass R h2 m i) hNX (@current_form_comass_real_norm R h2 m i)
  m (@coordinate_basis R m) (@coordinate_basisP R m) A hA EA va hEA
  (@current_smooth_derivatives R h2 m A hA i)
  (@current_smooth_derivative_laws R h2 m A hA i) K.
have hS:=@continuous_real_dual_member_continuous R DA
  (@current_test_opens R h2 m A hA i)
  (smooth_test_final_topology_laws hEA (@current_smooth_derivative_laws R h2 m A hA i)).1 S.
have hL:open_family_continuous
    (smooth_function_opens (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)))
    (norm_open_family (@scalar_absolute_value_norm R)) L.
  exact:(open_family_continuous_compose hM
    (open_family_continuous_compose hPull (open_family_continuous_compose hC hS))).
have[r [J [M0 [hM0 hBound]]]]:=(@smooth_dual_finite_bound R Z (A_m Z R^o (j+i)) NZ
  (@current_form_comass R h2 (m+n) (j+i)) hNZ
  (@current_form_comass_real_norm R h2 (m+n) (j+i)) Full (E (j+i))
  (@current_smooth_value R h2 (m+n) Full hFull (j+i))
  (@current_smooth_derivatives R h2 (m+n) Full hFull (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)) L).1 hL.
exists r,J,M0;split;first exact:hM0.
move=>psi;exact:(hBound psi).
Qed.
End CurrentCartesianProbeBound.
