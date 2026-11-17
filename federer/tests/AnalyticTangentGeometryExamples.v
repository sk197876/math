(** Federer (1969), 3.4.11, p. 338:
    actual translated full-plane, nonempty R^0 and original
    cusp regressions. Every original numbered-theorem premise
    is proved; the examples retain both dimension endpoints
    and the nonanalytic tangent obstruction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness SetGermUP SetGermCentreMember
  AnalyticVarietyGermUP FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary TangentConeUP
  TangentOpenDomain NormOpenDomainLaws AnalyticTangentGeometry AnalyticSetDimensionEndpoints
  HausdorffMeasure HausdorffCountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_translated_plane_tangent_majorant_regression]:
    the original finite polynomial theorem of 3.4.11,
    p. 338, at the actual nonzero centre
    (2,3) of the whole plane. Every resulting
    homogeneous majorant is the whole plane and has
    its actual original dimension two. *)
Example analytic_translated_plane_tangent_majorant_regression (R:realType):
  let X:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 2) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  let a:X:=[ffun i=>if i==ord0 then 2 else 3] in
  exists F:set (X->R),finite_set F /\
    (forall P,F P ->exists k,(0<k)%N /\@HomogeneousPolynomialFunctions.is_homogeneous_polynomial R X R^o k P) /\
    [set v|forall P,F P ->P v=0]=setT /\
    @analytic_set_dimension R 2 [set v|forall P,F P ->P v=0%R]= 2%N.
Proof.
move=>X NX hNX a.
have hAnalytic:@is_analytic_set_in R X NX hNX setT setT.
  move=>x _;exists setT,setT;split;first done.
  split;last reflexivity;exact:finite_analytic_variety_domain_whole openT.
have hNonempty:=@set_germ_centre_member_nonempty
  (Topological.clone (real_norm_metric_space hNX) _) a setT Logic.I.
have [F [hFinite [hPolynomial [hContain hBound]]]]:=
  @federer_3_4_11_finite_polynomial_majorant R 2 setT setT a openT (fun _ _=>Logic.I)
    hAnalytic Logic.I hNonempty.
exists F;split;first exact:hFinite.
split;first exact:hPolynomial.
have hWhole:[set v:X|forall P,F P ->P v=0]=setT.
  apply/seteqP;split;first by move=>x _.
  move=>v _;apply:hContain;rewrite (@norm_tangent_open_domain R X NX hNX setT a (@norm_full_domain_interior R X NX a));done.
split;first exact:hWhole.
rewrite hWhole;exact:analytic_set_whole_dimension.
Qed.

(** Source for [analytic_zero_ambient_tangent_majorant_regression]:
    the nonempty original R^0 case of 3.4.11,
    p. 338. A finite homogeneous majorant
    contains its actual tangent, has dimension zero,
    and retains the nonzero counting mass H^0=1. *)
Example analytic_zero_ambient_tangent_majorant_regression (R:realType):
  let X:=R_n R 0 in
  let hB:=@euclidean_inner_productP R 0 in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  exists F:set (X->R),finite_set F /\
    (norm_tangent_cone NX setT 0 `<=` [set v|forall P,F P ->P v=0]) /\
    @analytic_set_dimension R 0 [set v|forall P,F P ->P v=0%R]=0%N /\
    @hausdorff_measure R (inner_metric_space hB) 0 setT= 1%E.
Proof.
move=>X hB NX hNX.
have hAnalytic:@is_analytic_set_in R X NX hNX setT setT.
  move=>x _;exists setT,setT;split;first done.
  split;last reflexivity;exact:finite_analytic_variety_domain_whole openT.
have hNonempty:=@set_germ_centre_member_nonempty
  (Topological.clone (real_norm_metric_space hNX) _) (0:X) setT Logic.I.
have [F [hFinite [hPolynomial [hContain hBound]]]]:=
  @federer_3_4_11_finite_polynomial_majorant R 0 setT setT 0 openT (fun _ _=>Logic.I)
    hAnalytic Logic.I hNonempty.
exists F;split;first exact:hFinite.
split;first exact:hContain.
split.
- apply/eqP;by rewrite eqn_leq leq0n andbT;exact:analytic_set_dimension_bound.
- have hPoint:(@setT (inner_metric_space hB))=[set 0].
    apply/seteqP;split;last by move=>x _.
    move=>x _;exact:coordinate_zero x.
  rewrite hPoint;exact:hausdorff_zero_singleton.
Qed.

(** Source for [analytic_cusp_nonanalytic_tangent_regression]:
    the actual original cusp has finite analytic
    equations, its exact printed tangent half-axis, and
    a nonanalytic tangent germ, 3.4.11, p. 338. *)
Example analytic_cusp_nonanalytic_tangent_regression (R:realType):
  let X:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 2) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  @is_finite_analytic_variety R X NX hNX setT (@AnalyticCusp.set R) /\
  (forall v,norm_tangent_cone NX (@AnalyticCusp.set R) 0 v<->0<=v ord0 /\v ord_max=0) /\
  ~@is_analytic_variety_germ R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0
      (norm_tangent_cone NX (@AnalyticCusp.set R) 0)).
Proof.
move=>X NX hNX.
split;first exact:analytic_cusp_finite_variety.
split;[exact:analytic_cusp_tangent_equation|exact:analytic_cusp_tangent_germ_not_analytic].
Qed.
