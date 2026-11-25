(** Federer 2.10.27, p. 191: rescaling of the actual
    ball-section radius, supporting arbitrary centres and positive
    radii in the real-degree profile integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric InnerNormedTopology RealPower
  RealHausdorffBallCoefficient RealEuclideanBallSectionProfileUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Close Scope ereal_scope.

(** Source for [real_ball_section_radius_rescaling]: supporting
    homogeneity of the square-root section radius in Federer
    2.10.27, p. 191. The closed boundary d=r is retained. *)
Lemma real_ball_section_radius_rescaling (R:realType) (r d:R):
  0<r ->0<=d ->d<=r ->
  Num.sqrt (r^+2-d^+2)=r*Num.sqrt (1-(r^-1*d)^+2).
Proof.
move=> hr hd hdr.
have hrNe:r!=0:=lt0r_neq0 hr.
have hInv:0<r^-1 by rewrite invr_gt0.
have hScaled:r^-1*d<=1.
  have h:=ler_wpM2l (ltW hInv) hdr.
  by rewrite mulVf // in h.
have hSd:0<=r^-1*d:=mulr_ge0 (ltW hInv) hd.
have hD:0<=1-(r^-1*d)^+2.
  by rewrite subr_ge0 -(expr1n _ 2) (ler_sqr _ _) ?nnegrE ?hSd ?ler01.
have hEq:r^+2-d^+2=r^+2*(1-(r^-1*d)^+2).
  field;by rewrite hrNe.
by rewrite hEq sqrtrM ?sqr_ge0 // sqrtr_sqr (ger0_norm (ltW hr)).
Qed.

(** Source for [real_ball_section_profile_rescaling]: exact
    homogeneity of profiles specified by their independent value
    laws, underlying the first display of Federer 2.10.27,
    p. 191. No representation of the sealed profile is opened. *)
Lemma real_ball_section_profile_rescaling (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R) p q:
  0<r ->is_real_euclidean_ball_section_profile hk 0 1 p ->
  is_real_euclidean_ball_section_profile hk u r q ->forall y,
  q y=((real_power r k)%:E* p (r^-1*:(y-u)))%E.
Proof.
move=> hr hp hq y.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose v:=r^-1*:(y-u).
have hrNe:r!=0:=lt0r_neq0 hr.
have hInv:0<r^-1 by rewrite invr_gt0.
have hDist:mdist (0:X) v=r^-1*mdist u y.
  by rewrite !inner_metric_normE subr0 !inner_norm_topologyE /v
    inner_normZ (ger0_norm (ltW hInv)).
case:(leP (mdist u y) r)=>hy.
- have hScaled:mdist (0:X) v<=1.
    rewrite hDist;have h:=ler_wpM2l (ltW hInv) hy;by rewrite mulVf // in h.
  rewrite (real_ball_section_profile_inside hq hy)
    (real_ball_section_profile_inside hp hScaled) hDist expr1n -EFinM
    (@real_ball_section_radius_rescaling R r (mdist u y) hr (mdist_ge0 _ _) hy)
    real_power_product ?(ltW hr) ?sqrtr_ge0 //.
  congr (_%:E);ring.
- have hScaled:1<mdist (0:X) v.
    rewrite hDist.
    have h:r^-1*r<r^-1*mdist u y by rewrite ltr_pM2l.
    by rewrite mulVf // in h.
  by rewrite (real_ball_section_profile_outside hq hy)
    (real_ball_section_profile_outside hp hScaled) mule0.
Qed.
