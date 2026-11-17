(** Federer 2.10.27, p. 191: the coefficient in the
    real-degree profile integral is the actual alpha(k+m).
    Reuse the proved Gamma recurrence and original normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import EulerGamma EulerGammaRecurrence EulerGammaHalfParameters
  RealHausdorffNormalisation RealHausdorffBallCoefficient RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff SphereCoordinateParameters SphereCoordinateMoment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_ball_section_gamma_coefficient]: supporting
    exact coefficient cancellation in the first display of Federer
    2.10.27, p. 191. For real k>0 and natural m, the
    auxiliary (m+1)-ball moment yields precisely alpha(k+m);
    no alternative normalization or numerical Gamma estimate is used. *)
Lemma real_ball_section_gamma_coefficient (R:realType) m (k:R)
    (hk:0<k) (hk0:0<=k) (hq:-1<k-1):
  real_hausdorff_ball_coefficient hk0*(k/2)*
    ((2*euler_gamma (positive_coordinate_moment_parameter hq)*
      (euler_gamma_half R)^+(m.+1-1)/
      euler_gamma (@positive_coordinate_moment_denominator R m.+1 (k-1)
        (ltn0Sn m) hq))*((k-1)+m.+1%:R)^-1)=
  real_hausdorff_ball_coefficient (addr_ge0 hk0 (ler0n R m)).
Proof.
have hkm:0<k+m%:R by have hm:=ler0n R m;lra.
have hs:0<k/2 by apply:divr_gt0;lra.
have ht:0<(k+m%:R)/2 by apply:divr_gt0;lra.
have hGs:euler_gamma (positive_coordinate_moment_parameter hq)=euler_gamma hs.
  apply:gamma_equal_positive_parameters;field;lra.
have hGt:euler_gamma (@positive_coordinate_moment_denominator R m.+1 (k-1)
    (ltn0Sn m) hq)=euler_gamma ht.
  apply:gamma_equal_positive_parameters;rewrite -[m.+1]addn1 natrD;field;lra.
have hGK:euler_gamma (real_dimension_gamma_parameter hk0)=(k/2)*euler_gamma hs.
  exact:euler_gamma_recurrence.
have hGT:euler_gamma (real_dimension_gamma_parameter (addr_ge0 hk0 (ler0n R m)))=
    ((k+m%:R)/2)*euler_gamma ht.
  exact:euler_gamma_recurrence.
have hRad:(k-1)+m.+1%:R=k+m%:R by rewrite -[m.+1]addn1 natrD;ring.
have hGhalf:0<euler_gamma_half R:=euler_gamma_positive _.
have hPow:real_power (euler_gamma_half R) (k+m%:R)=
    real_power (euler_gamma_half R) k*(euler_gamma_half R)^+m.
  by rewrite real_power_add_exponents_positive //
    (@real_power_natural_exponent R (euler_gamma_half R) m (ltW hGhalf)).
rewrite /real_hausdorff_ball_coefficient hGK hGT hGs hGt hRad hPow subSS subn0.
have hsNe:k/2!=0:=lt0r_neq0 hs.
have htNe:(k+m%:R)/2!=0:=lt0r_neq0 ht.
have hkNe:k!=0:=lt0r_neq0 hk.
have hkmNe:k+m%:R!=0:=lt0r_neq0 hkm.
have hgsNe:euler_gamma hs!=0:=lt0r_neq0 (euler_gamma_positive hs).
have hgtNe:euler_gamma ht!=0:=lt0r_neq0 (euler_gamma_positive ht).
field;rewrite ?mulr_eq0 ?negb_or ?hsNe ?htNe ?hkNe ?hkmNe ?hgsNe ?hgtNe //;lra.
Qed.
