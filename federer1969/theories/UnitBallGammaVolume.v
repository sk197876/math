(** Federer (1969), 3.2.13, p. 251: Gamma formulas
    for alpha(m), derived from both proved sphere-mass formulas
    and the proved Gamma recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric HausdorffMeasure EuclideanBallVolume
  HausdorffUnitSphereMass SphereGammaMass EulerGamma EulerGammaRecurrence EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_dimension_half_successor]: positivity
    of (m/2)+1 in the alpha(m) formula,
    Federer 3.2.13, p. 251. *)
Lemma positive_dimension_half_successor (R:realType) m (hm:(0<m)%N):
  0<(m%:R:R)/2+1.
Proof. exact:addr_gt0 (@positive_dimension_half R m hm) ltr01. Qed.

(** Source for [euclidean_unit_ball_gamma_volume_product]: the
    first displayed Gamma quotient for alpha(m), Federer 3.2.13,
    p. 251, with denominator (m/2)Gamma(m/2). *)
Theorem euclidean_unit_ball_gamma_volume_product (R:realType) m (hm:(0<m)%N):
  euclidean_unit_ball_volume R m=(euler_gamma_half R)^+m/
    ((m%:R/2)*euler_gamma (@positive_dimension_half R m hm)).
Proof.
have hA:=@hausdorff_unit_sphere_mass R m hm.
have hG:=@hausdorff_unit_sphere_gamma_mass R m hm.
have hEq:=EFin_inj (eq_trans (esym hA) hG).
have hM:0<(m%:R:R) by rewrite ltr0n.
have hGamma:=euler_gamma_positive (@positive_dimension_half R m hm).
have hNe:euler_gamma (@positive_dimension_half R m hm)!= 0:=lt0r_neq0 hGamma.
have hScaled:=congr1 (fun v:R=>v*euler_gamma (@positive_dimension_half R m hm)) hEq.
rewrite divfK // in hScaled.
have hDen:0<(m%:R/2)*euler_gamma (@positive_dimension_half R m hm).
  apply:mulr_gt0=>//; exact:positive_dimension_half hm.
have hMul:euclidean_unit_ball_volume R m*((m%:R/2)*euler_gamma (@positive_dimension_half R m hm))=
    (euler_gamma_half R)^+m by nra.
have hQuot:=congr1 (fun v:R=>v/((m%:R/2)*euler_gamma (@positive_dimension_half R m hm))) hMul.
by rewrite mulfK ?gt_eqF in hQuot.
Qed.

(** Source for [euclidean_unit_ball_gamma_volume]: the final
    formula alpha(m)=Gamma(1/2)^m/Gamma((m/2)+1), Federer
    3.2.13, p. 251, for every positive integer dimension. *)
Theorem euclidean_unit_ball_gamma_volume (R:realType) m (hm:(0<m)%N):
  euclidean_unit_ball_volume R m=(euler_gamma_half R)^+m/
    euler_gamma (@positive_dimension_half_successor R m hm).
Proof.
have hRec:=euler_gamma_recurrence (@positive_dimension_half R m hm)
  (@positive_dimension_half_successor R m hm).
rewrite hRec; exact:euclidean_unit_ball_gamma_volume_product hm.
Qed.
