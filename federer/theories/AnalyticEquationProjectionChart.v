(** Federer (1969), 3.4.8(10), pp. 331–332:
    the prescribed p_m is an analytic
    coordinate map on the original regular
    zero system outside delta=0. Restrict
    the joint inverse to that open
    nonzero locus before taking its zero slice. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormRegularity NormClassZeroNonzeroLocus NormBoundedLinearTopology NormOpenDomainLaws
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormCoordinateSystemUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex EuclideanBlockLinearMaps
  FiniteAnalyticJointInverse PrescribedAnalyticSliceCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ProjectionChart.
Variable R:realType.
Variables m l:nat.
Local Notation X:=(R_n R (m+l)).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (m+l))).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (m+l))).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Variables A Z:set X.
Variable P:Hom X Y.
Hypothesis hP:norm_bounded_linear NX NY P.
Variable f:'I_l->X->R.
Variable delta:X->R.
Hypothesis hF:forall j,@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) A (f j).
Hypothesis hDelta:@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) A delta.
Hypothesis hZ:forall x,Z x <->A x /\(forall j,f j x = 0) /\delta x<>0.
Hypothesis hJoint:forall a,Z a ->exists D:'I_l->Hom X R^o,
  (forall j,has_norm_differential NX (fun t:R^o=>`|t|) A (f j) a (D j)) /\
  forall u,P u = 0 ->(forall j,D j u = 0) ->u=0.

(** Source for [analytic_equation_projection_chart]:
    each x in Z has a
    neighbourhood on which p_m restricted
    to Z is an analytic coordinate
    system, 3.4.8(10), pp. 331–332.
    The actual equations supply the differential;
    the existing analytic inverse theorem supplies
    the inverse. No local chart is assumed. *)
Theorem analytic_equation_projection_chart a:
  Z a ->exists (U:set X) (V:set Y) (psi:Y->X),
    U a /\(forall x,U x ->A x /\delta x<>0) /\is_inner_convex V /\
    @norm_analytic R X Y NX NY hNX hNY U P /\
    @norm_analytic R Y X NY NX hNY hNX V psi /\
    is_norm_coordinate_system hNX hNY Z U V P psi 1%N.
Proof.
move=>ha.
pose O:set X:=fun x=>A x /\delta x!=0.
have hOOpen:=@norm_class_zero_nonzero_locus_open R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) A delta
  (norm_class_continuous (norm_analytic_class_all_orders hDelta 0%N)).
have hO x (hx:O x):norm_domain_interior NX O x.
  have hNeighbourhood:=hOOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX O x).2 (hNeighbourhood x hx)).
have hOA:O `<=` A by move=>x hx;exact:hx.1.
have haO:O a.
  have h:=(@hZ a).1 ha;split;first exact:h.1.
  by apply/eqP;exact:h.2.2.
have hFRestricted j:=@norm_analytic_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) A O (f j) hOA hO (hF j).
have [D [hD hSeparate]]:=@hJoint a ha.
have hDRestricted j:has_norm_differential NX (fun t:R^o=>`|t|) O (f j) a (D j).
  exact:(@norm_differential_restrict R X R^o NX (fun t:R^o=>`|t|) A O (f j) a (D j)
    hOA (hO a haO) (hD j)).
have [H [G [r [hFirst [hLast [hH [hR [hInto [hInverse hG]]]]]]]]]:=
  @finite_analytic_joint_inverse R m l O hO P hP f hFRestricted a haO D hDRestricted hSeparate.
pose T:set X:=fun x=>NX (x-a)<r.
have haT:T a by rewrite /T subrr inner_norm0.
have hTa:norm_domain_interior NX T a:=@norm_open_ball_domain_interior R X NX hNX a r a haT.
have hPlane x (hx:T x):Z x <->@euclidean_last_block_map R m l (H x) = 0.
  split.
  - move=>hz;apply/ffunP=>j.
    rewrite hLast ffunE;exact:((@hZ x).1 hz).2.1 j.
  - move=>hZero;apply:(@hZ x).2;split;first exact:(@hInto x hx).1.
    split.
    + move=>j;have h:=congr1 (fun y:R_n R l=>y j) hZero.
      by rewrite hLast ffunE in h.
    + apply/eqP;exact:(@hInto x hx).2.
have hPrefix x (hx:T x):P x = @euclidean_first_block_map R m l (H x).
  exact:esym (hFirst x).
have [U [V [psi [hUa [hUT [hConvex [hForward [hBackward hChart]]]]]]]]:=
  @prescribed_analytic_slice_coordinates R m l Z T (H @` T) H G P a ha hTa hInverse hG hPlane hPrefix.
exists U,V,psi;split;first exact:hUa.
split.
- move=>x hx;have h:=@hInto x (hUT x hx);split;first exact:h.1.
  by apply/eqP;exact:h.2.
by split;first exact:hConvex.
Qed.
End ProjectionChart.
