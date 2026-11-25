(** Federer (1969), 3.4.11, p. 338:
    every tangent to the original cusp has zero
    second coordinate. The original equation y^2=x^3
    makes y^2 negligible in degree two; apply the
    proved homogeneous little-o tangent theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
From Federer Require Import Hom RealNormUP NormClassOneUP NormRegularity GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanScalarCoordinateMaps
  EuclideanScalarCoordinateAnalytic NormAnalyticUP NormAnalyticLocal NormAnalyticScalarProducts
  TangentConeUP HomogeneousLittleOTangent AnalyticCuspUP AnalyticCuspSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cusp_tangent_second_coordinate_zero]:
    the original tangent cone lies in the first
    coordinate axis, 3.4.11, p. 338. The
    actual cusp equation supplies the full two-dimensional
    negligible estimate, including the origin. *)
Theorem analytic_cusp_tangent_second_coordinate_zero (R:realType) (v:R_n R 2):
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R 2))
    (@AnalyticCusp.set R) 0 v ->v ord_max=0.
Proof.
move=>hTangent.
pose X:=R_n R 2;pose NX:=inner_norm (@euclidean_inner_productP R 2).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2).
pose P:=fun x:X=>(x ord_max)^+2.
have hAnalytic:=norm_analytic_scalar_power 2%N (@euclidean_scalar_coordinate_analytic R 2 ord_max).
have hContinuous:norm_class_zero NX (fun t:R^o=>`|t|) setT P.
  exact:(norm_class_continuous (norm_analytic_class_all_orders hAnalytic 0%N)).
have hScale (t:R) (x:X) (_:0<t):P (t*:x)=t^+2*P x.
  by rewrite /P ffunE;change ((t*x ord_max)^+2=t^+2*(x ord_max)^+2);rewrite exprMn.
have [C [hC hCoordinate]]:=@euclidean_scalar_coordinate_bounded R 2 ord0.
have hLittle (e:R) (he:0<e):exists r:R,0<r /\forall x,@AnalyticCusp.set R x ->
    NX x<r ->`|P x|<=e*(NX x)^+2.
  pose A:=C^+3.
  have hA:0<=A by rewrite /A;exact:exprn_ge0 hC.
  pose r:=e/(A+1).
  have hDen:0<A+1 by lra.
  have hr:0<r by rewrite /r divr_gt0.
  have hProduct:r*(A+1)=e by rewrite /r divfK ?gt_eqF.
  exists r;split;first exact:hr.
  move=>x /(@AnalyticCusp.laws R)=>hEquation hx.
  have hN:=real_seminorm_nonnegative hNX.1 x.
  have hCoordinateX:=hCoordinate x.
  change (is_true (`|x ord0|<=C*NX x)) in hCoordinateX.
  have hPower:=lerXn2r 3%N (normr_ge0 (x ord0)) (mulr_ge0 hC hN) hCoordinateX.
  rewrite exprMn in hPower.
  have hSmall:A*NX x<=e by nra.
  have hSquare:0<=(NX x)^+2:=exprn_ge0 _ hN.
  have hBound:=ler_wpM2r hSquare hSmall.
  rewrite /P -hEquation normrX.
  apply:le_trans hPower _.
  change (is_true (A*(NX x)^+3<=e*(NX x)^+2)).
  have hCube:(NX x)^+3=NX x*(NX x)^+2 by ring.
  rewrite hCube mulrA;exact:hBound.
have hZero:=@homogeneous_little_o_tangent_zero R X NX hNX (@AnalyticCusp.set R) P 2%N
  hContinuous hScale hLittle v hTangent.
apply/eqP;move/eqP:hZero;by rewrite /P sqrf_eq0.
Qed.
