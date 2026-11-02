(** Federer (1969), 3.2.28(2), printed p. 264:
    the tangent kernel of Q consists exactly of vertical
    skew-adjoint directions. The actual differential formula,
    horizontal isometry and orthogonal splitting prove this
    algebra before the geometric tangent identification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP FamilyUpdate Bilinear
  GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  EuclideanCoordinateTopology EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm InnerExterior InnerExteriorPositivity
  ExteriorGrading ExteriorNorm FiniteExteriorPowers OrthogonalMaps
  SymmetricEndomorphisms EuclideanRectangularAdjoint
  EuclideanHomInnerCharts EuclideanStiefelTangentSplit
  EuclideanGramDifferentialAlgebra EuclideanExteriorWordCoefficient
  EuclideanExteriorWordEvaluation ExteriorWordReplacementAlgebra
  EuclideanExteriorHorizontalPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Vertical.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation Y:=(exterior_power (R_n R n) m).

(** Source for [euclidean_exterior_vertical_differential_zero]:
    DQ(g)(g u)=0 for skew u, Federer 3.2.28(2), p. 264.
    Each replacement retains only the diagonal coefficient
    of u, which is zero by 1.7.3, pp. 29–30.
    No orthogonality of g is needed for this algebraic law. *)
Theorem euclidean_exterior_vertical_differential_zero (g:X) (L:Hom X Y):
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  forall u:Hom (R_n R m) (R_n R m),
    is_skewsymmetric_endomorphism (@euclidean_inner_product R m) (hom_as_linear u) ->
    L (hom_comp g u)=0.
Proof.
move=>hL u hu; rewrite hL; apply:big1=>i _.
rewrite euclidean_exterior_word_replacementE hom_compE.
have hLift:g (u (@coordinate_basis R m i))=
    \sum_(j<m) (u (@coordinate_basis R m i)) j *:g (@coordinate_basis R m j).
  change (hom_as_linear g (u (@coordinate_basis R m i))=
    \sum_(j<m) (u (@coordinate_basis R m i)) j *:g (@coordinate_basis R m j)).
  rewrite -{1}(euclidean_coordinate_expansion (u (@coordinate_basis R m i))) linear_sum.
  apply:eq_bigr=>j _; exact:linearZ.
rewrite hLift exterior_word_replacement_combination.
have hd:=@skewsymmetric_diagonal_zero R (R_n R m) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) (hom_as_linear u) hu (@coordinate_basis R m i).
rewrite euclidean_inner_basis in hd.
by rewrite hd scale0r.
Qed.

(** Source for [euclidean_exterior_horizontal_kernel_trivial]:
    the horizontal isometry has zero kernel, supporting
    rank DQ in Federer 3.2.28(2), p. 264. The exact
    inner-product equality, not a bound assumption, proves it. *)
Lemma euclidean_exterior_horizontal_kernel_trivial
    (h2:(1+1:R)!=0) (g:X) (L:Hom X Y):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  forall h,hom_comp (euclidean_rectangular_adjoint g) h=0 ->L h=0 ->h=0.
Proof.
move=>hg hL h hh hz.
have hp:=@euclidean_exterior_horizontal_differential_pairing R m n h2 g L hg hL h h hh hh.
rewrite hz (bil0l (inner_bilinear (@exterior_inner_productP R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m))) in hp.
apply/eqP; rewrite -(@inner_self_eq0 R X (@euclidean_hom_inner_product R m n)
  (@euclidean_hom_inner_productP R m n)).
apply/eqP; exact:esym hp.
Qed.

(** Source for [euclidean_exterior_tangent_kernel_vertical]:
    ker DQ on the Stiefel tangent space is the image of
    the skew endomorphisms under u to g u, Federer
    3.2.28(2), p. 264. The horizontal decomposition
    and its proved isometry discharge both implications. *)
Theorem euclidean_exterior_tangent_kernel_vertical
    (h2:(1+1:R)!=0) (g:X) (L:Hom X Y):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  (forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) ->
  forall h,euclidean_gram_differential g h=0 ->
    (L h=0 <->exists u:Hom (R_n R m) (R_n R m),
      is_skewsymmetric_endomorphism (@euclidean_inner_product R m) (hom_as_linear u) /\
      h=hom_comp g u).
Proof.
move=>hg hL h hh.
have [hZ [hU hSplit]]:=euclidean_stiefel_horizontal_split hg hh.
split.
- move=>hz.
  pose u:=hom_comp (euclidean_rectangular_adjoint g) h.
  pose z:=h-hom_comp g u.
  have hVz:L (hom_comp g u)=0:=euclidean_exterior_vertical_differential_zero hL hU.
  have hLz:L z=0.
    have ht:=congr1 L hSplit.
    change (L h=L (z+hom_comp g u)) in ht.
    rewrite linearD /= hVz addr0 hz in ht.
    exact:esym ht.
  have hZero:z=0:=euclidean_exterior_horizontal_kernel_trivial h2 hg hL hZ hLz.
  exists u; split; first exact hU.
  by change (h=z+hom_comp g u) in hSplit; rewrite hZero add0r in hSplit.
- move=>[u [hu hEq]]; rewrite hEq.
  exact:(euclidean_exterior_vertical_differential_zero hL hu).
Qed.
End Vertical.
