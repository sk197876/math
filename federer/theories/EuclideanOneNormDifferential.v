(** Federer (1969), 3.2.6, p. 245: in a scalar
    source the area Jacobian is the norm of the actual
    curve derivative. The scalar and one-coordinate Euclidean
    lines are identified by their existing inverse maps. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate CoordinateProjection
  InnerNorm InnerNormInequalities HilbertFormCompactness NormDifferentialUP NormDifferentialScalar
  NormedCurveDerivativeUP EuclideanLinearJacobian EuclideanOrthonormalJacobian OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_one_norm_coordinate]: supporting
    isometric identification R=R^1 for Federer 3.2.6,
    p. 245, using the norm specification of 1.7.1. *)
Lemma euclidean_one_norm_coordinate (R:realType) (x:R_n R 1):
  inner_norm (@euclidean_inner_productP R 1) x=`|x ord0|.
Proof.
apply:inner_norm_value; first exact:normr_ge0.
by rewrite -normrX ger0_norm ?sqr_ge0 // /euclidean_inner_product big_ord1 expr2.
Qed.

(** Source for [euclidean_one_differential_curve_iff]: the
    identification of Df and f' in the first formula of
    Federer 3.2.6, p. 245. Both sides are actual
    derivatives; the whole scalar domain has interior everywhere. *)
Theorem euclidean_one_differential_curve_iff (R:realType) n
    (f:R->R_n R n) a (L:Hom (R_n R 1) (R_n R n)):
  has_norm_differential (inner_norm (@euclidean_inner_productP R 1))
    (inner_norm (@euclidean_inner_productP R n)) setT
    (fun x=>f (euclidean_one_project x)) (euclidean_one_embed a) L <->
  has_normed_curve_derivative (inner_norm (@euclidean_inner_productP R n))
    f a (L (@coordinate_basis R 1 ord0)).
Proof.
pose NY:=inner_norm (@euclidean_inner_productP R n).
have hLinear:linear (fun t:R^o=>L (euclidean_one_embed t)).
  move=>c t s; have he:euclidean_one_embed (c*t+s)=c*:euclidean_one_embed t+euclidean_one_embed s.
    by apply/ffunP=>i; rewrite /euclidean_one_embed !ffunE.
  by rewrite he linearD linearZ.
pose M:=@HomMap R R^o (R_n R n) (fun t=>L (euclidean_one_embed t))
  (introT (asboolP _) hLinear).
have hBasis:euclidean_one_embed (1:R)=@coordinate_basis R 1 ord0.
  apply/ffunP=>i; by rewrite /euclidean_one_embed /coordinate_basis !ffunE (ord1 i) eqxx.
have hEval:M 1=L (@coordinate_basis R 1 ord0) by change (L (euclidean_one_embed 1)=L (@coordinate_basis R 1 ord0)); rewrite hBasis.
split.
- move=>hD.
  have hScalar:has_norm_differential (fun t:R^o=>`|t|) NY setT f a M.
    constructor.
    + exists 1; split; first exact:ltr01; by [].
    + have [C [hC hb]]:=norm_differential_bounded hD.
      exists C; split=>// t; change (is_true (NY (L (euclidean_one_embed t))<=C*`|t|)).
      have hh:=hb (euclidean_one_embed t).
      by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE in hh.
    + move=>e he; have [d [hd hb]]:=norm_differential_remainder hD he.
      exists d; split=>// t _ ht.
      have hSmall:inner_norm (@euclidean_inner_productP R 1) (euclidean_one_embed t)<d.
        by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE.
      have hh:=hb (euclidean_one_embed t) Logic.I hSmall.
      have hAdd:euclidean_one_project (euclidean_one_embed a+euclidean_one_embed t)=a+t.
        by rewrite /euclidean_one_project /euclidean_one_embed !ffunE.
      rewrite hAdd euclidean_one_embedK euclidean_one_norm_coordinate /euclidean_one_embed ffunE in hh.
      exact hh.
  have hh:=(@norm_differential_real_source R (R_n R n) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f a M).1 hScalar.
  by rewrite hEval in hh; exact hh.2.
- move=>hCurve.
  have hInterior:norm_domain_interior (fun t:R^o=>`|t|) setT a.
    exists 1; split; first exact:ltr01; by [].
  have hScalar:has_norm_differential (fun t:R^o=>`|t|) NY setT f a M.
    apply:(@norm_differential_real_source R (R_n R n) NY
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f a M).2.
    by split=>//; rewrite hEval.
  constructor.
  + exists 1; split; first exact:ltr01; by [].
  + have [C [hC hb]]:=norm_differential_bounded hScalar.
    exists C; split=>// x.
    have hh:=hb (euclidean_one_project x).
    change (is_true (NY (L (euclidean_one_embed (euclidean_one_project x)))<=C*`|euclidean_one_project x|)) in hh.
    by rewrite euclidean_one_projectK -euclidean_one_norm_coordinate in hh.
  + move=>e he; have [d [hd hb]]:=norm_differential_remainder hScalar he.
    exists d; split=>// x _ hx.
    have hSmall:`|euclidean_one_project x|<d by rewrite -euclidean_one_norm_coordinate.
    have hh:=hb (euclidean_one_project x) Logic.I hSmall.
    change (is_true (NY (f (a+euclidean_one_project x)-f a-L (euclidean_one_embed (euclidean_one_project x)))<=e*`|euclidean_one_project x|)) in hh.
    have hAdd:euclidean_one_project (euclidean_one_embed a+x)=a+euclidean_one_project x.
      by rewrite /euclidean_one_project /euclidean_one_embed !ffunE.
    by rewrite euclidean_one_projectK -euclidean_one_norm_coordinate -hAdd -{2}(euclidean_one_embedK a) in hh.
Qed.

(** Source for [euclidean_one_linear_jacobian]: the factor
    |f'| in Federer 3.2.6, p. 245, is the
    degree-one Jacobian of its linear differential, by 1.7.6.
    No nonzero derivative or positive target dimension is assumed. *)
Lemma euclidean_one_linear_jacobian (R:realType) n
    (L:Hom (R_n R 1) (R_n R n)):
  euclidean_linear_jacobian 1 L=inner_norm (@euclidean_inner_productP R n)
    (L (@coordinate_basis R 1 ord0)).
Proof.
have ho:orthonormal_family (@euclidean_inner_product R 1) (@coordinate_basis R 1).
  by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hOrth (i j:'I_1):i!=j -> @euclidean_inner_product R n (L (@coordinate_basis R 1 i)) (L (@coordinate_basis R 1 j))=0.
  by rewrite (ord1 i) (ord1 j) eqxx.
by rewrite (@euclidean_jacobian_orthogonal_frame_images R 1 n L (@coordinate_basis R 1) ho hOrth) big_ord1.
Qed.
