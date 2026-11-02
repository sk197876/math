(** Federer (1969), 3.2.3, pp. 243–244: the
    singular-differential graph estimate uses an orthonormal
    source basis adapted to the differential, as supplied
    by 1.7.3, p. 30. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom HomogeneousHom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm OrthonormalFamilies InnerExterior InnerExteriorPositivity InnerExteriorTriangular
  FiniteExteriorPowers ExteriorGrading ExteriorNorm ExteriorOperatorNorm ExteriorOperatorEstimate
  ExteriorHadamardEquality TopExteriorNorm EuclideanLinearMaps EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_jacobian_orthonormal_frame]: the
    exterior norm description of J_m in Federer 3.2.3,
    p. 244, through 1.7.6. Every orthonormal source
    m-frame supplies a unit top exterior vector. *)
Lemma euclidean_jacobian_orthonormal_frame (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m):
  orthonormal_family (@euclidean_inner_product R m) e ->
  euclidean_linear_jacobian m L=exterior_norm (euclidean_two_nonzero R)
    (@euclidean_inner_productP R n) (e_lambda (fun i=>L (e i)) (ord_tuple m)).
Proof.
move=>ho.
pose w:=e_lambda e (ord_tuple m).
have hw:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) w= 1.
  exact (orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) ho).
rewrite /euclidean_linear_jacobian (@top_exterior_operator_unit_value R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m
  (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear L) w hw).
by rewrite /w exterior_map_indexed_product.
Qed.

(** Source for [euclidean_jacobian_orthogonal_frame_images]:
    the product of singular lengths used in the graph
    estimate of Federer 3.2.3, p. 244, by 1.7.3
    and the orthogonal product norm of 1.7.5. *)
Lemma euclidean_jacobian_orthogonal_frame_images (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m):
  orthonormal_family (@euclidean_inner_product R m) e ->
  (forall i j,i!=j -> @euclidean_inner_product R n (L (e i)) (L (e j))=0) ->
  euclidean_linear_jacobian m L=\prod_i inner_norm (@euclidean_inner_productP R n) (L (e i)).
Proof.
move=>ho hImages; rewrite (euclidean_jacobian_orthonormal_frame L ho).
exact (orthogonal_product_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) hImages).
Qed.

(** Source for [noninjective_orthogonal_frame_zero_image]:
    a zero singular direction in the second case of
    Federer 3.2.3, p. 244. In an adapted full
    orthonormal frame, noninjectivity forces a zero image. *)
Lemma noninjective_orthogonal_frame_zero_image (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m):
  orthonormal_family (@euclidean_inner_product R m) e ->
  (forall i j,i!=j -> @euclidean_inner_product R n (L (e i)) (L (e j))=0) ->
  ~injective L -> exists i,L (e i)=0.
Proof.
move=>ho hImages hL; apply:contrapT=>hNone; apply:hL.
apply:(euclidean_linear_jacobian_top_positive L).1.
rewrite (@euclidean_jacobian_orthogonal_frame_images R m n L e ho hImages).
apply:prodr_gt0=>i _; rewrite inner_norm_gt0.
apply/negP=>/eqP hi; apply:hNone; by exists i.
Qed.
