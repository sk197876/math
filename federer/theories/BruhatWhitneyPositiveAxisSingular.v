(** Federer (1969), 3.4.10, p. 338:
    every positive z-axis point is nonregular on
    the actual cited surface. Its three actual tangent
    directions contradict the existing manifold tangent-plane theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormBoundedLinearTopology
  TangentConeUP TangentConeLocal SubmanifoldTangentPlane AnalyticSubmanifoldUP
  AnalyticRegularLocusUP AnalyticRegularLocusSealed AnalyticSetDimension
  BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed BruhatWhitneySurfaceDimension
  BruhatWhitneyAxis BruhatWhitneyPositiveTangents BruhatWhitneyTangentPlaneObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_positive_axis_singular]: the
    positive half-axis lies in the original surface
    minus its regular part, supporting the nonanalyticity
    example cited by 3.4.10, p. 338. *)
Theorem bruhat_whitney_positive_axis_singular (R:realType) (b:R):
  0<b ->~@AnalyticRegularLocus.value R 3
    (@analytic_set_dimension R 3 (@BruhatWhitneySurface.set R))
    setT (@BruhatWhitneySurface.set R) (@bruhat_whitney_axis R b).
Proof.
move=>hb;rewrite bruhat_whitney_surface_dimension=>hRegular.
pose X:=R_n R 3.
pose NX:=inner_norm (@euclidean_inner_productP R 3).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3).
pose S:=@BruhatWhitneySurface.set R.
pose a:=@bruhat_whitney_axis R b.
have [ha [U [hU [haU [hUT hManifold]]]]]:=
  (@AnalyticRegularLocus.laws R 3 2 setT S a).1 hRegular.
have hInterior:norm_domain_interior NX U a.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX U a).2.
  have h:=hU;rewrite openE in h;exact:h a haU.
have [W hPlane]:=@submanifold_tangent_plane R 3 2 1 (S `&` U) a
  (leqnn 1) (analytic_submanifold_class_one hManifold) (conj ha haU).
rewrite (norm_tangent_open_restriction S hInterior) in hPlane.
pose s:=Num.sqrt b.
have hS:s^+2=b:=sqr_sqrtr (ltW hb).
have hPositive:0<s by rewrite /s sqrtr_gt0.
have hNonzero:s!=0 by rewrite (gt_eqF hPositive).
have hPlus:=@bruhat_whitney_signed_curve_tangent R b s hS.
have hMinus:=@bruhat_whitney_signed_curve_tangent R b (-s).
have hMinusSquare:(-s)^+2=b by rewrite expr2 mulrN mulNr opprK -expr2 hS.
have hMinusTan:=hMinus hMinusSquare.
have hAxis:=@bruhat_whitney_axis_tangent R b.
rewrite hPlane in hPlus hMinusTan hAxis.
exact:(@bruhat_whitney_tangent_plane_obstruction R b s W hNonzero hPlus hMinusTan hAxis).
Qed.
