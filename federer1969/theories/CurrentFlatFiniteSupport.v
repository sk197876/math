(** Federer (1969), 4.1.12, p. 367: finite
    flat functionals have their original support
    in K. Reuse compact closedness and the preceding
    derivative-locality theorem on original test functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothFunctionSupport SmoothDerivativeSeminormUP
  SmoothDerivativeSeminormLaws SmoothDerivativeSupport SmoothTestSpaces LinearSubspaceRepresentationUP
  RealSeminormOperations SeminormRealDualBound DistributionLocalBound OpenFamilyTopologyUP NormOpenTopology
  SmoothTestTopology ContinuousRealDual CurrentFlatFormSeminormLaws CurrentFlatFormOrderBound
  CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic CurrentFlatFiniteContinuity
  NormMetric FunctionalSupportUP SmoothLocalSupport CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatFiniteSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation DK := (smooth_fixed_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation fixed := (smooth_fixed_test_inclusion hE).
Local Notation step := (smooth_test_step hE).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation Dual := (@CurrentFlatDualSeminorm.value R h2 n m U hU K).
Local Notation RO := (norm_open_family (@scalar_absolute_value_norm R)).

Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation support := (@smooth_functional_support R X Y NX hNX U DT value).
Local Notation hK := (smooth_compact_is_compact K).

(** Source for [current_finite_flat_functional_support]: a
    finite original F_K functional has support in K,
    the first observation of Federer 4.1.12, p. 367.
    The proof uses annihilation off K and the actual
    vanishing of all derivatives off test support. *)
Theorem current_finite_flat_functional_support (T:Hom DT R^o):
  (Dual T < +oo)%E->support T `<=` smooth_compact_carrier K.
Proof.
move=>hFinite x [hUx hSupport].
case:(pselect (smooth_compact_carrier K x))=>// hOutside.
apply:False_ind;apply:hSupport.
exists [set y|~smooth_compact_carrier K y];split;last exact:hOutside.
split.
- exact:closed_openC (compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) hK).
- move=>phi hPhi.
  have [a [ha hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K T hFinite.
  have hBound:=@current_flat_dual_finite_bound R h2 n m U hU K T a hValue phi.
  have [C [hC hOrder]]:=@current_flat_form_order_one_bound R h2 n m U hU K.
  have hZero:nu K 1%N (inc phi)=0.
    apply:(@smooth_seminorm_disjoint_support_zero R X Y NX NY hNX hNY U hU E ev D hD
      K 1%N (nu K 1%N) (smooth_function_derivative_seminorm_laws hD K 1%N) (inc phi)).
    move=>y hy hTest.
    change (@smooth_function_support R X Y NX hNX U DT value phi y) in hTest.
    exact:(hPhi y hTest) hy.
  have hFlat:Flat phi<=0.
    rewrite /current_flat_test_seminorm.
    have h:=hOrder (inc phi).
    by rewrite hZero mulr0 in h.
  have hFinal:=le_trans hBound (ler_wpM2l ha hFlat).
  rewrite mulr0 in hFinal.
  apply/eqP;by rewrite -normr_eq0 eq_le hFinal normr_ge0.
Qed.

(** Source for [current_finite_flat_supported_current]: every
    algebraic functional with finite F_K is an actual
    original current supported in K, Federer 4.1.12,
    p. 367. Continuity and support are conclusions. *)
Theorem current_finite_flat_supported_current (T:Hom DT R^o):
  (Dual T < +oo)%E->exists S:@current_space R h2 n U hU m,
    @current_value R h2 n U hU m S=T /\
    @current_support R h2 n U hU m S `<=` smooth_compact_carrier K.
Proof.
move=>hFinite.
have [S hValue]:=@current_finite_flat_functional_represents R h2 n m U hU K T hFinite.
exists S;split;first exact:hValue.
have hSupport:=current_finite_flat_functional_support hFinite.
by rewrite -hValue in hSupport.
Qed.
End CurrentFlatFiniteSupport.
