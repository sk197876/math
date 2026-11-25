(** Federer (1969), 3.2.28(2)–(3), printed pp. 264–266:
    proved normal coordinate existence, using only the public
    sealed orthogonal projection-chart laws from 1.7.4,
    pp. 30–31. The witness maps remain local to this proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP OrthogonalMaps AdjointUP
  CoordinateProjection EuclideanRectangularAdjoint
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps
  EuclideanRightBlockProjection OrthogonalProjectionChartUP
  OrthogonalProjectionChart OrthogonalProjectionChartLaws EuclideanFrameComplementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_frame_complement_block_exists]:
    an m-frame in R^(k+m) has a k-dimensional orthogonal
    complement, supporting Federer 3.2.28(2)–(3),
    pp. 264–266, by the orthogonal coordinates of 1.7.4,
    p. 31. Empty frames and complements are retained. *)
Theorem euclidean_frame_complement_block_exists (R:realType) k m
    (g:Hom (R_n R m) (R_n R (k+m))):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R (k+m)) (hom_as_linear g) ->
  exists (a:Hom (R_n R k) (R_n R (k+m)))
    (p:Hom (R_n R (k+m)) (R_n R k)),is_euclidean_frame_complement g a p.
Proof.
move=>hg.
pose q:=hom_as_linear (euclidean_rectangular_adjoint g).
have hq:O_star q.
  exists (hom_as_linear g); split; first exact hg.
  exact:euclidean_rectangular_adjoint_pairing.
pose D:=@orthogonal_projection_chart R k m q hq.
have hD:=@orthogonal_projection_chart_specification R k m q hq.
change (is_orthogonal_projection_chart q D.1 D.2) in hD.
pose a:=hom_comp (hom_of_linear D.2) (@euclidean_first_injection_map R k m).
pose p:=hom_comp (@euclidean_first_block_map R k m) (hom_of_linear D.1).
exists a,p; constructor.
- move=>u v.
  change (euclidean_inner_product (D.2 (@euclidean_first_injection R k m u))
    (D.2 (@euclidean_first_injection R k m v))=euclidean_inner_product u v).
  rewrite (projection_chart_backward_orthogonal hD) /euclidean_first_injection
    euclidean_block_join_inner /= (bil0l (inner_bilinear (@euclidean_inner_productP R m))) addr0.
  reflexivity.
- move=>u; change (@euclidean_first_block R k m
    (D.1 (D.2 (@euclidean_first_injection R k m u)))=u).
  by rewrite (projection_chart_backward_inverse_law hD) euclidean_first_block_injectionK.
- move=>u.
  exact:(@projection_chart_fibre_coordinate R k m q D.1 D.2 hD u 0).
- move=>x hx.
  change (D.2 (@euclidean_first_injection R k m
    (@euclidean_first_block R k m (D.1 x)))=x).
  have hLast:@euclidean_last_block R k m (D.1 x)=0.
    change (@euclidean_right_block R k m (D.1 x)=0).
    by rewrite (projection_chart_coordinate_law hD).
  have hRec:=@euclidean_block_linear_decomposition R k m (D.1 x).
  have hZero:@euclidean_last_injection R k m 0=0.
    change (@euclidean_last_injection_map R k m 0=0); exact:linear0.
  rewrite hLast hZero addr0 in hRec.
  by rewrite -hRec (projection_chart_forward_inverse_law hD).
Qed.

(** Source for [euclidean_frame_complement_exists]: an
    orthogonal m-frame in R^n has n-m normal coordinates,
    supporting dim Z(g) and the tangent bases in Federer
    3.2.28(2)–(3), pp. 264–266. The displayed m<=n
    hypothesis permits the exact natural dimension subtraction. *)
Theorem euclidean_frame_complement_exists (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  (m<=n)%N ->is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  exists (a:Hom (R_n R (n-m)) (R_n R n))
    (p:Hom (R_n R n) (R_n R (n-m))),is_euclidean_frame_complement g a p.
Proof.
move=>hm; move:g; rewrite -(subnK hm).
move=>g hg.
have hd:((n-m)+m-m)%N=(n-m)%N by rewrite addnK.
rewrite hd.
exact:euclidean_frame_complement_block_exists hg.
Qed.
