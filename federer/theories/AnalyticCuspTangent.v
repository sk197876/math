(** Federer (1969), 3.4.11, p. 338:
    the exact original cusp tangent is the positive
    first-coordinate half-axis. Actual polynomial tangent witnesses,
    the coordinate obstructions and the established cone
    scaling law prove both directions, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness TangentConeUP TangentConeBasic AnalyticCuspUP AnalyticCuspSealed
  AnalyticCuspCoordinateSign AnalyticCuspPositiveTangent AnalyticCuspVerticalTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_cusp_tangent_equation]: the
    exact original display Tan(S,0)={x:x_1>=0,x_2=0},
    3.4.11, p. 338. The actual
    cusp equation and actual tangent definition remain. *)
Theorem analytic_cusp_tangent_equation (R:realType) (v:R_n R 2):
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R 2))
    (@AnalyticCusp.set R) 0 v <->0<=v ord0 /\v ord_max=0.
Proof.
split.
- move=>hTangent;split.
  + exact:analytic_cusp_tangent_first_coordinate_nonnegative hTangent.
  + exact:analytic_cusp_tangent_second_coordinate_zero hTangent.
- move=>[hNonnegative hVertical].
  have hVector:v=v ord0*:@coordinate_basis R 2 ord0.
    apply/ffunP=>i;case:i=>[[|[|i]] hi].
    + have hEq:(@Ordinal 2 0 hi)=ord0 by apply:val_inj.
      rewrite hEq /coordinate_basis !ffunE /=.
      change (v ord0=v ord0*1);by rewrite mulr1.
    + have hEq:(@Ordinal 2 1 hi)=ord_max by apply:val_inj.
      rewrite hEq /coordinate_basis !ffunE /=.
      change (v ord_max=v ord0*0);by rewrite mulr0 hVertical.
    + exfalso;by move:hi;rewrite !ltnS ltn0.
  rewrite hVector.
  exact:(@norm_tangent_nonnegative_scale R (R_n R 2)
    (inner_norm (@euclidean_inner_productP R 2))
    (inner_norm_real_norm (@euclidean_inner_productP R 2)) (@AnalyticCusp.set R) 0
    (@coordinate_basis R 2 ord0) (v ord0) (@analytic_cusp_positive_axis_tangent R) hNonnegative).
Qed.
