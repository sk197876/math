(** Federer (1969), 3.2.28(2), printed p. 264:
    DQ(g) preserves the actual Hom inner product on
    Z(g)={h:g* h=0}. This is proved by the orthogonal
    single-replacement words in the actual derivative. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP FamilyUpdate Bilinear GrassmannAbbreviations
  FiniteCoordinates CoordinateProjection EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm InnerExterior InnerExteriorPositivity
  ExteriorGrading ExteriorNorm FiniteExteriorPowers OrthogonalMaps
  OrthonormalFamilies HomInner HomInnerCoordinates EuclideanRectangularAdjoint
  EuclideanHomInnerCharts EuclideanStiefelInnerSplitting
  EuclideanExteriorWordCoefficient EuclideanExteriorWordEvaluation
  OrthonormalWordReplacementInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Horizontal.
Variable R:realType.
Variables m n:nat.
Variable h2:(1+1:R)!=0.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation Y:=(exterior_power (R_n R n) m).
Local Notation BX:=(@euclidean_hom_inner_product R m n).
Local Notation BY:=(@exterior_inner_form R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m).
Local Notation hBY:=(@exterior_inner_productP R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m).

(** Source for [euclidean_stiefel_horizontal_frame_orthogonal]:
    g* h=0 means every h(e_j) is normal to every g(e_i),
    by 1.7.4, p. 30. Supporting the subspace Z(g) in
    Federer 3.2.28(2), p. 264. *)
Lemma euclidean_stiefel_horizontal_frame_orthogonal (g h:X):
  hom_comp (euclidean_rectangular_adjoint g) h=0 ->
  forall i j, euclidean_inner_product
    (g (@coordinate_basis R m i)) (h (@coordinate_basis R m j))=0.
Proof.
move=>hz i j.
have he:=congr1 (fun L:Hom (R_n R m) (R_n R m)=>L (@coordinate_basis R m j)) hz.
change (euclidean_rectangular_adjoint g (h (@coordinate_basis R m j))=0) in he.
by rewrite -euclidean_rectangular_adjoint_pairing he
  (bil0r (inner_bilinear (@euclidean_inner_productP R m))).
Qed.

(** Source for [euclidean_exterior_horizontal_differential_pairing]:
    the horizontal part of DQ(g) is an isometry, Federer
    3.2.28(2), p. 264. The supplied map is specified by
    the proved actual single-replacement derivative formula;
    this supporting algebra uses no extra geometric hypothesis. *)
Theorem euclidean_exterior_horizontal_differential_pairing (g:X) (L:Hom X Y):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  forall h k,
    hom_comp (euclidean_rectangular_adjoint g) h=0 ->
    hom_comp (euclidean_rectangular_adjoint g) k=0 ->
    BY (L h) (L k)=BX h k.
Proof.
move=>hg hL h k hh hk.
have ho:orthonormal_family (@euclidean_inner_product R n)
    (fun i=>g (@coordinate_basis R m i)).
  move=>i j; rewrite hg.
  exact:(@euclidean_coordinate_orthonormal_family R m i j).
have hH:=euclidean_stiefel_horizontal_frame_orthogonal hh.
have hK:=euclidean_stiefel_horizontal_frame_orthogonal hk.
rewrite !hL.
rewrite (big_morph (fun x=>BY x (\sum_(j<m)
    euclidean_exterior_word_coefficient (family_with (i:=j) [ffun _:'I_m=>g] k)))
  (fun x y=>bilDl (inner_bilinear hBY) x y _) (bil0l (inner_bilinear hBY) _)).
rewrite /euclidean_hom_inner_product.
rewrite (@hom_inner_orthonormal_sum R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  (@euclidean_coordinate_orthonormal_family R m)).
apply:eq_bigr=>i _.
rewrite (big_morph (fun y=>BY
    (euclidean_exterior_word_coefficient (family_with (i:=i) [ffun _:'I_m=>g] h)) y)
  (bilDr (inner_bilinear hBY) _) (bil0r (inner_bilinear hBY) _)).
rewrite (bigD1 i) //=.
have hDiag:=@orthonormal_replacement_pairing_diagonal R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m
  (fun j=>g (@coordinate_basis R m j)) ho i
  (h (@coordinate_basis R m i)) (k (@coordinate_basis R m i))
  (fun j=>hH j i) (fun j=>hK j i).
have hMain:BY
    (euclidean_exterior_word_coefficient (family_with (i:=i) [ffun _: 'I_m=>g] h))
    (euclidean_exterior_word_coefficient (family_with (i:=i) [ffun _: 'I_m=>g] k))=
      euclidean_inner_product (h (@coordinate_basis R m i)) (k (@coordinate_basis R m i)).
  by rewrite !euclidean_exterior_word_replacementE hDiag.
rewrite hMain.
have hRest:(\sum_(j<m|j!=i) BY
    (euclidean_exterior_word_coefficient (family_with (i:=i) [ffun _:'I_m=>g] h))
    (euclidean_exterior_word_coefficient (family_with (i:=j) [ffun _:'I_m=>g] k)))=0.
  apply:big1=>j hji; rewrite !euclidean_exterior_word_replacementE.
  apply:(@orthonormal_replacement_pairing_off_diagonal R h2 (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m
    (fun a=>g (@coordinate_basis R m a)) ho i j
    (h (@coordinate_basis R m i)) (k (@coordinate_basis R m j))).
  - by rewrite eq_sym.
  - exact:(fun a=>hH a i).
by rewrite hRest addr0.
Qed.
End Horizontal.
