(** Federer (1969), 3.2.28(3), printed p. 265:
    complete alpha by an actual unit normal vector,
    using the proved opaque normal-coordinate laws.
    The erratum makes alpha a source-space frame. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CoordinateProjection EuclideanCoordinateTopology OrthogonalMaps
  EuclideanRectangularAdjoint EuclideanFrameComplementUP EuclideanFrameComplementExistence
  EuclideanHyperplaneNormalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hyperplane_normal_exists]: the
    adapted e_m used in Federer 3.2.28(3), p. 265.
    Its existence, unit length and exact normal line
    follow from a one-dimensional orthogonal complement;
    no global orientation choice is made. *)
Theorem euclidean_hyperplane_normal_exists (R:realType) k
    (alpha:Hom (R_n R k) (R_n R k.+1)):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->exists w,is_euclidean_hyperplane_normal alpha w.
Proof.
move=>hA.
have hExists:=@euclidean_frame_complement_exists R k k.+1 alpha (leqnSn k) hA.
rewrite subSnn in hExists.
have [a [p hComp]]:=hExists.
pose e:=@coordinate_basis R 1 ord0.
pose w:=a e.
have hOrtho:=frame_complement_orthogonal hComp.
have hE:euclidean_inner_product e e= 1.
  by rewrite euclidean_inner_basis /e /coordinate_basis ffunE eqxx.
have hCoordinate (u:R_n R 1):u=(u ord0:R)*:e.
  by rewrite -{1}(euclidean_coordinate_expansion u) big_ord1.
exists w; constructor.
- exact:eq_trans (hOrtho e e) hE.
- exact:frame_complement_normal hComp e.
- move=>z hz.
  have hRange:a (p z)=z:=frame_complement_range hComp hz.
  have hLine:a (p z)=((p z) ord0:R)*:w.
    have hLin:=congr1 a (hCoordinate (p z)).
    by rewrite linearZ in hLin.
  have hPair:=hOrtho (p z) e.
  change (euclidean_inner_product (a (p z)) w=euclidean_inner_product (p z) e) in hPair.
  rewrite hRange euclidean_inner_basis in hPair.
  by rewrite hPair -hLine hRange.
Qed.
