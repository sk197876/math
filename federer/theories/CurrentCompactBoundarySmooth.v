(** Federer (1969), 4.1.9, p. 363: compact point currents
    and their boundaries act on original smooth forms in the
    passage from current to form homotopy. Reuse the original
    unique smooth-dual extension and the continuous exterior
    derivative from 4.1.7, pp. 355–356. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentEvaluation CurrentBoundary CurrentBoundarySupport CurrentSupportGeometry SmoothCompactSet
  CurrentCompactExtensionUP CurrentCompactExtensionSealed CurrentCompactSmoothValue
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces
  SmoothDualRestriction ContinuousRealDual ContinuousRealDualTranspose
  CurrentTestExteriorDerivative SmoothCurrentExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactBoundarySmooth.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (fun k=>@current_smooth_space R h2 n U hU k).
Local Notation ev := (fun k=>@current_smooth_value R h2 n U hU k).
Local Notation hE := (fun k=>@current_smooth_space_laws R h2 n U hU k).
Local Notation hD := (fun k=>@current_smooth_derivative_laws R h2 n U hU k).
Local Notation O := (fun k=>smooth_function_opens (hD k)).
Local Notation hO := (fun k=>(smooth_function_topology_laws (hD k)).1).
Local Notation e := (fun k=>@continuous_real_dual_evaluation R (E k) (O k) (hO k)).
Local Notation rho := (fun k=>@current_smooth_dual_restriction R h2 n U hU k).
Local Notation d := (@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation hd := (@smooth_current_exterior_derivative_continuous R h2 n m U hU).
Variable T:@current_space R h2 n U hU m.+1.
Hypothesis hCompact:@compact (real_norm_metric_space hNX)
  [set x|@current_support R h2 n U hU m.+1 T x].
Local Notation B := (@current_boundary R h2 n m U hU T).

(** Source for [current_compact_boundary_compact]: the boundary
    of an original compactly supported current is compactly
    supported, supporting the point-current form argument in
    Federer 4.1.9, p. 363, by the support inclusion
    in 4.1.7, pp. 356–359. *)
Theorem current_compact_boundary_compact:
  @compact (real_norm_metric_space hNX) [set x|@current_support R h2 n U hU m B x].
Proof.
pose K:=@Build_smooth_compact_set R X NX hNX U
  (@current_support R h2 n U hU m.+1 T) (fun x hx=>hx.1) hCompact.
exact:(@current_support_compact_bound R h2 n m U hU K B
  (@current_boundary_support_subset R h2 n m U hU T)).
Qed.
Local Notation LB := (@CompactCurrentExtension.value R h2 n m U hU B current_compact_boundary_compact).
Local Notation LT := (@CompactCurrentExtension.value R h2 n m.+1 U hU T hCompact).

(** Source for [current_compact_boundary_smooth_value]: the
    actual extended boundary satisfies boundary T(phi)=T(d phi)
    for every smooth phi, supporting Federer 4.1.9,
    p. 363. The original restriction law and its
    uniqueness prove this extension, without assuming density
    or a new action on noncompact tests. *)
Theorem current_compact_boundary_smooth_value (phi:E m):
  @current_compact_smooth_value R h2 n m U hU B current_compact_boundary_compact phi=
    @current_compact_smooth_value R h2 n m.+1 U hU T hCompact (d phi).
Proof.
pose P:=@continuous_real_dual_transpose R (E m) (E m.+1) (O m) (O m.+1) (hO m) (hO m.+1) d hd.
have hRestriction:rho m (P LT)=B.
  apply:(@current_values_extensional R h2 n m U hU)=>psi.
  have hValue:=@smooth_dual_test_restriction_evaluation R X (A_m X R^o m)
    NX (@current_form_comass R h2 n m) hNX (@current_form_comass_real_norm R h2 n m)
    U (E m) (ev m) (hE m) (@current_smooth_derivatives R h2 n U hU m) (hD m) (P LT) psi.
  have hTranspose:=@continuous_real_dual_transpose_evaluation R (E m) (E m.+1)
    (O m) (O m.+1) (hO m) (hO m.+1) d hd LT (smooth_test_inclusion (hE m) psi).
  have hTest:=@current_compact_smooth_test_value R h2 n m.+1 U hU T hCompact
    (@current_test_exterior_derivative R h2 n m U hU psi).
  rewrite current_test_exterior_derivative_inclusion in hTest.
  exact:(eq_trans hValue (eq_trans hTranspose (eq_trans hTest
    (esym (@current_boundary_evaluation R h2 n m U hU T psi))))).
have hEqual:LB=(P LT:@current_smooth_dual_space R h2 n U hU m).
  apply:(@current_compact_extension_unique R h2 n m U hU B).
  - exact:(@CompactCurrentExtension.laws R h2 n m U hU B current_compact_boundary_compact).
  - exact:hRestriction.
change (e m LB phi=e m.+1 LT (d phi)).
rewrite hEqual.
exact:(@continuous_real_dual_transpose_evaluation R (E m) (E m.+1)
  (O m) (O m.+1) (hO m) (hO m.+1) d hd LT phi).
Qed.
End CurrentCompactBoundarySmooth.
