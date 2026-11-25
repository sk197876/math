(** Federer (1969), 3.3.4, p. 291:
    actual projective balls are the original
    single-coordinate cones in the active
    (m+1)-space. The actual adjoint inverse
    gives the rotated coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm InnerMetric OrthogonalMaps
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  EuclideanBlockLinearMaps CoordinateProjection EuclideanCoordinateMetric StructureBlockCone StructureProjectiveDirections
  StructureProjectiveAngleEquation SymmetricGrading InnerSymmetricPositivity
  SymmetricSquareGeometry InnerUnitNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_active_projective_ball_cone]:
    the actual equality between projective
    ball preimages and I_j in Federer
    3.3.4, p. 291. The distinguished
    normal axis is the first active
    coordinate and all m remaining coordinates
    are retained. The cone itself forces
    a nonzero projected vector, so no
    spurious direction is used at zero. *)
Theorem structure_active_projective_ball_cone (R:realType) m
    (h:Hom (R_n R (1+m)) (R_n R (1+m))) (u:R_n R (1+m)) (t:R):
  is_orthogonal_map (@euclidean_inner_product R (1+m))
    (@euclidean_inner_product R (1+m)) (hom_as_linear h) ->0<t ->
  (0<inner_norm (@euclidean_inner_productP R (1+m)) u /\
    inner_norm (@symmetric_inner_productP R (R_n R (1+m))
      (@euclidean_inner_product R (1+m)) (@euclidean_inner_productP R (1+m)) 2)
      (inner_projective_square (inner_unit_normalization (@euclidean_inner_productP R (1+m)) u)-
       inner_projective_square (h (@coordinate_basis R (1+m) (lshift m (ord0:'I_1)))))<t <->
    ((t^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m)
        (@euclidean_last_block R 1 m (euclidean_rectangular_adjoint h u)))^+2<
      ((euclidean_rectangular_adjoint h u) (lshift m (ord0:'I_1)))^+2).
Proof.
move=>hH ht.
pose hB:=@euclidean_inner_productP R (1+m).
pose N:=inner_norm hB.
pose i0:=lshift m (ord0:'I_1).
pose v:=euclidean_rectangular_adjoint h u.
pose a:=(inner_norm (@euclidean_inner_productP R m) (@euclidean_last_block R 1 m v))^+2.
pose b:=(v i0)^+2.
have hA:0<=a:=sqr_ge0 _.
have hB0:0<=b:=sqr_ge0 _.
have hInv:=euclidean_orthogonal_adjoint_orthogonal hH.
have hEnergy:(N u)^+2=a+b.
  have hSplit:=@structure_block_squared_norm R 1 m v.
  have hFirst:(inner_norm (@euclidean_inner_productP R 1) (@euclidean_first_block R 1 m v))^+2=b.
    by rewrite inner_norm_sqr /euclidean_inner_product big_ord1 /euclidean_first_block ffunE /b expr2.
  have hTail:(\sum_i ((@euclidean_last_block R 1 m v) i)^+2)=a.
    rewrite /a inner_norm_sqr /euclidean_inner_product.
    apply:eq_bigr=>i _; exact:expr2.
  rewrite hFirst hTail /v (orthogonal_map_norm hB hB hInv) in hSplit.
  by rewrite /N; nra.
have hUnit:N (h (@coordinate_basis R (1+m) i0))= 1.
  exact:(eq_trans (orthogonal_map_norm hB hB hH (@coordinate_basis R (1+m) i0))
    (@euclidean_coordinate_unit_norm R (1+m) i0)).
have hAxis:euclidean_inner_product u (h (@coordinate_basis R (1+m) i0))=v i0.
  rewrite (inner_symmetric hB) -euclidean_rectangular_adjoint_pairing.
  rewrite (inner_symmetric hB).
  exact:euclidean_inner_basis.
split.
- move=>[hu hBall].
  have hAngle:=(structure_projective_direction_ball hu hUnit ht).1 hBall.
  rewrite hAxis -/b -/N hEnergy in hAngle.
  apply:(structure_projective_angle_equation a b ht).1; nra.
- move=>hCone.
  have hPositive:0<a+b.
    apply:contrapT=>hNo.
    have hZero:a+b=0 by apply/eqP; rewrite eq_le; apply/andP; split; [by rewrite leNgt; apply/negP|exact:addr_ge0 hA hB0].
    have ha:a=0 by nra.
    have hb:b=0 by nra.
    by move:hCone; rewrite -/a -/b ha hb mulr0 ltxx.
  have hu:0<N u.
    have hNonnegative:0<=N u:=inner_norm_nonnegative _ _.
    nra.
  split=>//; apply:(structure_projective_direction_ball hu hUnit ht).2.
  rewrite hAxis -/b -/N hEnergy.
  have hAngle:=(structure_projective_angle_equation a b ht).2 hCone.
  nra.
Qed.
