(** Federer (1969), 3.2.28(2), printed p. 264:
    the actual continuous differential field of Q, together
    with its horizontal isometry. Only existence and exact
    laws are exposed; no global chosen field is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness
  ExteriorGrading ExteriorNorm InnerExterior InnerExteriorPositivity
  EuclideanRectangularAdjoint OrthogonalMaps
  EuclideanHomInnerCharts EuclideanExteriorWordCoefficient
  EuclideanExteriorWordSmooth EuclideanExteriorHorizontalPairing
  NormDifferentialUP NormDifferentialDirectional NormClassOneUP NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Field.
Variable R:realType.
Variables m n:nat.
Variable h2:(1+1:R)!=0.
Local Notation X:=(Hom (R_n R m) (R_n R n)).
Local Notation Y:=(exterior_power (R_n R n) m).
Local Notation NX:=(inner_norm (@euclidean_hom_inner_productP R m n)).
Local Notation NY:=(@exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_hom_inner_productP R m n)).
Local Notation hNY:=(inner_norm_real_norm
  (@exterior_inner_productP R h2 (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) m)).

(** Source for [euclidean_exterior_word_class_one_field_exists]:
    the differential field DQ in Federer 3.2.28(2),
    p. 264, is continuous and has the exact replacement
    formula. Smoothness and uniqueness of 3.1.1,
    pp. 209–210, discharge both existence obligations. *)
Theorem euclidean_exterior_word_class_one_field_exists:
  exists D:X->Hom X Y,
    is_norm_class_one_field NX NY (fun _=>True) (@euclidean_exterior_word_map R m n) D /\
    forall g h,D g h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h).
Proof.
have [D hD]:=(norm_class_firstP hNX hNY (fun _=>True)
  (@euclidean_exterior_word_map R m n)).1
  (@euclidean_exterior_word_smooth R m n h2 1%N).
exists D; split; first exact hD.
move=>g h.
have [L [hL hLe]]:=@euclidean_exterior_word_differential_exists R m n h2 g.
have hEq:=@norm_differential_unique R X Y NX NY hNX hNY (fun _=>True)
  (@euclidean_exterior_word_map R m n) g (D g) L
  (@norm_class_one_differential R X Y NX NY (fun _=>True)
    (@euclidean_exterior_word_map R m n) D hD g Logic.I) hL.
by rewrite hEq hLe.
Qed.

(** Source for [euclidean_exterior_word_horizontal_isometry_exists]:
    |DQ(g)h|=|h| on Z(g), Federer 3.2.28(2), p. 264.
    The field is the actual differential just proved, and
    the metric is the Hilbert Hom metric of 1.7.9, p. 35.
    The statement retains all natural degrees. *)
Theorem euclidean_exterior_word_horizontal_isometry_exists:
  exists D:X->Hom X Y,
    is_norm_class_one_field NX NY (fun _=>True) (@euclidean_exterior_word_map R m n) D /\
    (forall g h,D g h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _:'I_m=>g] h)) /\
    forall g,
      is_orthogonal_map (@euclidean_inner_product R m)
        (@euclidean_inner_product R n) (hom_as_linear g) ->
      forall h,hom_comp (euclidean_rectangular_adjoint g) h=0 ->
        NY (D g h)=NX h.
Proof.
have [D [hD hDe]]:=euclidean_exterior_word_class_one_field_exists.
exists D; split; first exact hD.
split; first exact hDe.
move=>g hg h hh.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr.
symmetry; exact:(@euclidean_exterior_horizontal_differential_pairing R m n h2
  g (D g) hg (hDe g) h h hh hh).
Qed.
End Field.
