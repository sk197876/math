(** Federer 3.2.45, p. 279: the printed linear modulus in
    reciprocal exponent fails for every finite proposed constant.
    The actual three-dimensional unit segment and the exact
    projection moment suffice; the continuity claim is separate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateMetric IntegralGeometricMeasure ProjectionBeta ProjectionThreeOneMoment
  ConvexExponentSecantCounterexample RealPower RealPowerDivision RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [convex_exponent_no_finite_secant_constant]: source
    correction for the final quantitative estimate in Federer
    3.2.45, p. 279. For each real gamma>0 choose t= 2gamma+1,
    u=0 and v= 1/t. On the actual unit segment all original
    Q_t equal one, but the normalized ratio exceeds the printed
    (gamma/beta_1)^(v-u). Thus enlarging the coarse finite gamma
    cannot repair that estimate. The continuity theorem is not refuted. *)
Theorem convex_exponent_no_finite_secant_constant (R:realType) (hmn:(1<=3)%N)
    (gamma:R):
  0<gamma ->exists t:R,
    1<=t /\0<t^-1<= 1 /\
    real_power (gamma/(@projection_beta R 3 1 hmn (1:R)%:E)) t^-1<
      (@projection_beta R 3 1 hmn t%:E)^-1.
Proof.
move=> hGamma.
pose t:= 2*gamma+1.
have ht:1<=t by rewrite /t;lra.
have htPos:0<t:=lt_le_trans ltr01 ht.
have htInv:0<t^-1 by rewrite invr_gt0.
have htInvLe:t^-1<= 1 by rewrite invf_le1.
exists t;split=> //;split;first by rewrite htInv htInvLe.
have htE:(1<=t%:E)%E by rewrite lee_fin.
have hBeta:=@projection_beta_positive R 3 1 hmn t%:E htE.
have hInv:0<(@projection_beta R 3 1 hmn t%:E)^-1 by rewrite invr_gt0.
have hMoment:=@projection_three_one_moment R hmn t ht.
have hInvPower:real_power ((@projection_beta R 3 1 hmn t%:E)^-1) t=t+1.
  by rewrite real_power_inverse_base // hMoment invrK.
have hCoef:gamma/(@projection_beta R 3 1 hmn (1:R)%:E)= 2*gamma.
  rewrite projection_three_one_first;field;by rewrite ?pnatr_eq0.
have hCoefPos:0<gamma/(@projection_beta R 3 1 hmn (1:R)%:E).
  rewrite hCoef;apply:mulr_gt0=> //;by rewrite ltr0n.
have hRoot:=@real_power_inverse_power R _ t (ltW hCoefPos) htPos.
rewrite ltNge;apply/negP=> hBad.
have hOrder:=@real_power_monotone R ((@projection_beta R 3 1 hmn t%:E)^-1)
  (real_power (gamma/(@projection_beta R 3 1 hmn (1:R)%:E)) t^-1) t
  (ltW hInv) hBad htPos.
rewrite hInvPower hRoot hCoef /t in hOrder;lra.
Qed.
