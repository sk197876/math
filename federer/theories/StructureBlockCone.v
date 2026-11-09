(** Federer (1969), 3.3.4, p. 289: the exact
    cone equation in the coordinates of an actual
    orthogonal frame. The original centre, projection,
    strict radius and every normal-coordinate square remain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanBlockProjection
  EuclideanProjectionSpace StructureCone StructureProjectionKernel StructureProjectionCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_block_squared_norm]: the
    split sum of squares in the first two displays
    of Federer 3.3.4, p. 289. Empty blocks are
    retained and the ambient Euclidean norm is actual. *)
Lemma structure_block_squared_norm (R:realType) m k (x:R_n R (m+k)):
  (inner_norm (@euclidean_inner_productP R (m+k)) x)^+2=
    (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k x))^+2+
    \sum_i ((@euclidean_last_block R m k x) i)^+2.
Proof.
rewrite inner_norm_sqr (@euclidean_block_split_inner R m k)
  -(inner_norm_sqr (@euclidean_inner_productP R m)).
by congr (_+_); rewrite /euclidean_inner_product; apply:eq_bigr=>i _.
Qed.

(** Source for [structure_frame_cone_square_equation]:
    the second cone display in Federer 3.3.4,
    p. 289. The actual orthogonal coordinate map
    f and the first-coordinate evaluation law for
    p give the literal normal-coordinate square sum.
    Such frame and projection witnesses stay local. *)
Theorem structure_frame_cone_square_equation (R:realType) m k
    (hmn:(m<=m+k)%N)
    (f:{linear R_n R (m+k)->R_n R (m+k)})
    (p:euclidean_projection_space R (m+k) m)
    (a x:inner_metric_space (@euclidean_inner_productP R (m+k)))
    (r: \bar R) (s:R):
  is_orthogonal_map (@euclidean_inner_product R (m+k))
    (@euclidean_inner_product R (m+k)) f ->
  (forall y,euclidean_projection_linear p y=@euclidean_first_block R m k (f y)) ->
  0<s ->
  (structure_cone (structure_projection_kernel hmn p) a r s x <->
    ((s^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f (x-a))))^+2<
      \sum_i ((@euclidean_last_block R m k (f (x-a))) i)^+2 /\
    ((inner_norm (@euclidean_inner_productP R (m+k)) (x-a))%:E<r)%E).
Proof.
move=>hF hP hs; rewrite structure_projection_coneE hP.
have hN:=inner_norm_nonnegative (@euclidean_inner_productP R (m+k)) (x-a).
have hP0:=inner_norm_nonnegative (@euclidean_inner_productP R m)
  (@euclidean_first_block R m k (f (x-a))).
have hLeft:0<=s^-1*inner_norm (@euclidean_inner_productP R m)
    (@euclidean_first_block R m k (f (x-a))).
  apply:mulr_ge0=>//; by rewrite invr_ge0 ltW.
have hEnergy:=structure_block_squared_norm (f (x-a)).
rewrite (orthogonal_map_norm (@euclidean_inner_productP R (m+k))
  (@euclidean_inner_productP R (m+k)) hF) in hEnergy.
have hAngle:
    s^-1*inner_norm (@euclidean_inner_productP R m)
      (@euclidean_first_block R m k (f (x-a)))<
        inner_norm (@euclidean_inner_productP R (m+k)) (x-a) <->
    ((s^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f (x-a))))^+2<
      \sum_i ((@euclidean_last_block R m k (f (x-a))) i)^+2.
  rewrite -(ltr_sqr hLeft hN) exprMn hEnergy.
  split=>h; nra.
by rewrite hAngle.
Qed.
