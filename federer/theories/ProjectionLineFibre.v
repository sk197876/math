(** Federer (1969), 3.2.35, p. 272:
    each actual codimension-one orthogonal fibre is
    an isometric affine line with a unique scalar
    parameter, from independent proved normal laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectionLineNormalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_line_normal_norm]: the
    actual unit length of the fibre direction
    in the boundary-fibre argument of Federer
    3.2.35, p. 272. The squared unit
    normal law implies the existing nonnegative
    norm is exactly one. *)
Lemma projection_line_normal_norm (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w:
  is_projection_line_normal p w ->inner_norm (@euclidean_inner_productP R k.+1) w= 1.
Proof.
move=>hW; apply:inner_norm_value; first exact:ler01.
by rewrite expr1n (@projection_line_normal_unit R k p w hW).
Qed.

(** Source for [projection_line_fibre]: the actual
    affine line underlying N(p restricted to Bdry S,y)=2
    in Federer 3.2.35, p. 272. The
    exact kernel spanning law gives every fibre
    point and linearity gives the reverse inclusion.
    The base point may be any point on the
    original fibre, including a chosen member of S. *)
Lemma projection_line_fibre (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w a x:
  is_projection_line_normal p w ->
  (euclidean_projection_linear p x=euclidean_projection_linear p a <->
    exists t:R,x=a+t*:w).
Proof.
move=>hW; split.
- move=>hx.
  have hZero:euclidean_projection_linear p (x-a)=0 by rewrite linearB hx subrr.
  have hSpan:=@projection_line_normal_span R k p w hW (x-a) hZero.
  exists (euclidean_inner_product (x-a) w).
  by rewrite -hSpan addrC subrK.
- move=>[t ->].
  rewrite linearD linearZ (@projection_line_normal_kernel R k p w hW).
  change (euclidean_projection_linear p a+t*:(0:R_n R k)=euclidean_projection_linear p a).
  by rewrite scaler0 addr0.
Qed.

(** Source for [projection_line_distance]: supporting
    the scalar line-section topology and boundedness
    in Federer 3.2.35, p. 272. The
    actual affine parametrization preserves precisely
    the scalar absolute-value distance, rather than
    only supplying an unspecified Lipschitz constant. *)
Lemma projection_line_distance (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w (a:R_n R k.+1) (t s:R):
  is_projection_line_normal p w ->
  mdist (a+t*:w:inner_metric_space (@euclidean_inner_productP R k.+1)) (a+s*:w)=`|t-s|.
Proof.
move=>hW.
have hDifference:(a+t*:w)-(a+s*:w)=(t-s)*:w.
  by rewrite opprD addrACA subrr add0r -scalerBl.
by rewrite inner_metric_distanceE hDifference inner_normZ
  (@projection_line_normal_norm R k p w hW) mulr1.
Qed.

(** Source for [projection_line_parameter_injective]: the
    two distinct endpoint parameters give distinct
    actual boundary points in Federer 3.2.35,
    p. 272. This follows from the proved
    line isometry and scalar positive definiteness. *)
Lemma projection_line_parameter_injective (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) w (a:R_n R k.+1):
  is_projection_line_normal p w ->injective (fun t:R=>a+t*:w).
Proof.
move=>hW t s he.
have hDistance:=@projection_line_distance R k p w a t s hW.
rewrite he mdistxx in hDistance.
apply/eqP; rewrite -subr_eq0 -normr_eq0; apply/eqP; exact:esym hDistance.
Qed.
