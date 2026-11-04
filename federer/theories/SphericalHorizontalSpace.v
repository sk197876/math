(** Federer (1969), 3.2.47, p. 283: the actual
    horizontal complement W(g), its rank-one lift characterization,
    and the exact norm scale of D Phi. No tangent splitting,
    dimension, derivative or norm scale is assumed in its definition. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra classical_sets.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm OrthogonalMaps EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra EuclideanGramTangentAlgebra
  SphericalHorizontalLift EuclideanStiefelHalfNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_horizontal_space]: the printed W(g)
    in 3.2.47, p. 283: the Gram tangent kernel
    intersected with the orthogonal complement of the kernel
    of actual evaluation w to w(c). The Gram kernel is
    the already proved actual tangent of 3.2.28, p. 263. *)
Definition spherical_horizontal_space (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c:R_n R N):=
  [set w:Hom (R_n R N) (R_n R N)|euclidean_gram_differential g w=0 /\
    forall z,euclidean_gram_differential g z=0 ->z c=0 ->euclidean_hom_inner_product w z=0].

(** Source for [spherical_horizontal_lift_member]: the actual
    rank-one lift is orthogonal to every vertical tangent,
    supporting the printed W(g) in 3.2.47, p. 283. *)
Lemma spherical_horizontal_lift_member (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c v:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  spherical_horizontal_space g c (spherical_horizontal_lift g c v).
Proof.
move=>hg; split; first exact (@spherical_horizontal_lift_tangent R N g c v hg).
move=>z hz hValue; rewrite (@spherical_horizontal_lift_pairing R N g z c v hg hz) hValue
  (bil0r (inner_bilinear (@euclidean_inner_productP R N))) mulr0; reflexivity.
Qed.

(** Source for [spherical_gram_tangent_evaluation_perpendicular]: the
    actual derivative sends every Gram tangent into the tangent
    hyperplane to the sphere at g(c), supporting 3.2.47,
    p. 283. *)
Lemma spherical_gram_tangent_evaluation_perpendicular (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  euclidean_gram_differential g w=0 ->euclidean_inner_product (g c) (w c)=0.
Proof.
move=>hw.
have hPair:=@euclidean_gram_differential_pairing R N N g w c c.
rewrite hw hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R N)))
  (inner_symmetric (@euclidean_inner_productP R N) (w c) (g c)) in hPair.
by nra.
Qed.

(** Source for [spherical_horizontal_lift_characterization]: every
    horizontal w is exactly the lift of its original
    derivative value w(c), proving the splitting used in
    3.2.47, p. 283, from orthogonality alone. *)
Theorem spherical_horizontal_lift_characterization (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_inner_product c c= 1 ->spherical_horizontal_space g c w ->
  w=spherical_horizontal_lift g c (w c).
Proof.
move=>hg hc [hw hOrthogonal].
pose h:=spherical_horizontal_lift g c (w c).
pose z:=w-h.
have hPerpendicular:euclidean_inner_product (g c) (w c)=0.
  exact (@spherical_gram_tangent_evaluation_perpendicular R N g w c hw).
have hTangent:euclidean_gram_differential g h=0.
  exact (@spherical_horizontal_lift_tangent R N g c (w c) hg).
have hValue:h c=w c.
  exact (@spherical_horizontal_lift_evaluation R N g c (w c) hc hPerpendicular).
have hZTangent:euclidean_gram_differential g z=0.
  change (euclidean_gram_differential g (w-h)=0).
  exact (eq_trans (linB (hom_linear (euclidean_gram_differential g)) w h)
    (eq_trans (congr2 (fun a b:Hom (R_n R N) (R_n R N)=>a-b) hw hTangent)
      (subrr (0:Hom (R_n R N) (R_n R N))))).
have hZValue:z c=0.
  have hEval:=linB (@hom_eval_linear R (R_n R N) (R_n R N) c) w h.
  exact (eq_trans hEval (eq_trans (congr1 (fun a=>w c-a) hValue) (subrr (w c)))).
have hWZ:euclidean_hom_inner_product w z=0:=hOrthogonal z hZTangent hZValue.
have hHZ:euclidean_hom_inner_product h z=0.
  rewrite /h (@spherical_horizontal_lift_pairing R N g z c (w c) hg hZTangent) hZValue
    (bil0r (inner_bilinear (@euclidean_inner_productP R N))) mulr0; reflexivity.
have hZero:euclidean_hom_inner_product z z=0.
  rewrite /z (bilBl (inner_bilinear (@euclidean_hom_inner_productP R N N))).
  by rewrite -/z hWZ hHZ subrr.
have hZ:z=0.
  apply/eqP; rewrite -(inner_self_eq0 (@euclidean_hom_inner_productP R N N)) hZero eqxx; reflexivity.
apply/eqP; rewrite -subr_eq0; apply/eqP; exact hZ.
Qed.

(** Source for [spherical_horizontal_square]: the actual horizontal
    squared norm is twice the squared norm of the actual
    evaluation differential, 3.2.47, p. 283. *)
Theorem spherical_horizontal_square (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_inner_product c c= 1 ->spherical_horizontal_space g c w ->
  euclidean_hom_inner_product w w= 2*euclidean_inner_product (w c) (w c).
Proof.
move=>hg hc hw.
have hPerpendicular:=@spherical_gram_tangent_evaluation_perpendicular R N g w c hw.1.
have hSquare:=@spherical_horizontal_lift_square R N g c (w c) hg hc hPerpendicular.
exact (eq_trans (congr2 (@euclidean_hom_inner_product R N N)
  (@spherical_horizontal_lift_characterization R N g w c hg hc hw)
  (@spherical_horizontal_lift_characterization R N g w c hg hc hw)) hSquare).
Qed.

(** Source for [spherical_horizontal_norm_scale]: the EXACT
    printed scale |D Phi(g)w|=2^(-1/2)|w| on
    W(g), 3.2.47, p. 283. The actual
    norms and all their nonnegativity premises are retained. *)
Theorem spherical_horizontal_norm_scale (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_inner_product c c= 1 ->spherical_horizontal_space g c w ->
  inner_norm (@euclidean_inner_productP R N) (w c)=
    (Num.sqrt (2:R))^-1*inner_norm (@euclidean_hom_inner_productP R N N) w.
Proof.
move=>hg hc hw.
have [hPositive hCoefficient]:=euclidean_stiefel_half_normalization R.
apply:inner_norm_value.
- exact:mulr_ge0 (ltW hPositive) (inner_norm_nonnegative _ _).
- rewrite exprMn inner_norm_sqr (@spherical_horizontal_square R N g w c hg hc hw) expr2.
  have hRearrange:(Num.sqrt (2:R))^-1*(Num.sqrt (2:R))^-1*
      (2*euclidean_inner_product (w c) (w c))=
      (2*(Num.sqrt (2:R))^-1*(Num.sqrt (2:R))^-1)*euclidean_inner_product (w c) (w c) by ring.
  by rewrite hRearrange hCoefficient mul1r.
Qed.
