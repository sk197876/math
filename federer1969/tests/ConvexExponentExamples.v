(** Concrete source-estimate regressions for Federer 3.2.45,
    p. 279: an actual unit segment refutes the quantitative
    claim both at and away from reciprocal exponent zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateMetric IntegralGeometricMeasure ProjectionBeta ProjectionThreeOneMoment
  ConvexExponentSecantCounterexample RealPower RealPowerNaturalHausdorff RealPowerHalfNatural.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [unit_segment_zero_reciprocal_regression]: concrete
    source-correction regression for Federer 3.2.45, p. 279.
    All original Q_t values are one on the actual segment, yet
    u=0 and v= 1/2 violate the printed coarse-gamma-one bound. *)
Example unit_segment_zero_reciprocal_regression (R:realType) (hmn:(1<=3)%N):
  (forall t: \bar R,(1<=t)%E ->
    @convex_integral_geometric_measure R 3 1 hmn t
      (@euclidean_coordinate_line R 3 ord0 0 @` `[(0%R:R),1%R])= 1%E) /\
  Num.sqrt (2:R)<(@projection_beta R 3 1 hmn (2:R)%:E)^-1.
Proof.
have [hValues hBad]:=@convex_exponent_secant_counterexample R hmn.
split=> //.
rewrite convex_exponent_printed_coarse_gamma_one projection_three_one_first in hBad.
have hCoef:(1/(1/2):R)= 2 by field;by rewrite ?pnatr_eq0.
have hTwo:(0<2:>R) by lra.
by rewrite hCoef (RealPowerHalfNatural.real_power_positive_square_root hTwo) in hBad.
Qed.

(** Source for [unit_segment_positive_reciprocal_regression]: concrete
    source-correction regression for Federer 3.2.45, p. 279.
    At u= 1/16 and v= 1/8 the sixteenth power of the actual
    normalized Q ratio is 81/17, exceeding the printed upper
    bound's sixteenth power two. Removing u=0 alone does not
    repair the quantitative assertion. *)
Example unit_segment_positive_reciprocal_regression (R:realType) (hmn:(1<=3)%N):
  ((@projection_beta R 3 1 hmn (16:R)%:E)/
    (@projection_beta R 3 1 hmn (8:R)%:E))^+16=81/17 /\
  (2:R)<((@projection_beta R 3 1 hmn (16:R)%:E)/
    (@projection_beta R 3 1 hmn (8:R)%:E))^+16.
Proof.
have h8:(1:R)<=8 by lra.
have h16:(1:R)<= 16 by lra.
have h8E:(1<=(8:R)%:E)%E by rewrite lee_fin.
have h16E:(1<=(16:R)%:E)%E by rewrite lee_fin.
have hM8:=@projection_three_one_moment R hmn 8 h8.
have hM16:=@projection_three_one_moment R hmn 16 h16.
have hP8:0<=@projection_beta R 3 1 hmn (8:R)%:E:=ltW (@projection_beta_positive R 3 1 hmn (8:R)%:E h8E).
have hP16:0<=@projection_beta R 3 1 hmn (16:R)%:E:=ltW (@projection_beta_positive R 3 1 hmn (16:R)%:E h16E).
have hPow8:(@projection_beta R 3 1 hmn (8:R)%:E)^+8=(8+1:R)^-1.
  by rewrite -(@real_power_natural_exponent R _ 8 hP8).
have hPow16:(@projection_beta R 3 1 hmn (16:R)%:E)^+16=(16+1:R)^-1.
  by rewrite -(@real_power_natural_exponent R _ 16 hP16).
have hDen:(@projection_beta R 3 1 hmn (8:R)%:E)^+16=((8+1:R)^-1)^+2.
  change ((@projection_beta R 3 1 hmn (8:R)%:E)^+(8*2)%N=((8+1:R)^-1)^+2).
  by rewrite exprM hPow8.
have hRatio:((@projection_beta R 3 1 hmn (16:R)%:E)/
    (@projection_beta R 3 1 hmn (8:R)%:E))^+16=81/17.
  rewrite exprMn exprVn hPow16 hDen;field;by rewrite ?pnatr_eq0.
split=> //;rewrite hRatio;lra.
Qed.
