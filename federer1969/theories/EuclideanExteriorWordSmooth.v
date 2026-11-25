(** Federer (1969), 3.2.28(2), printed p. 264:
    Q(g)=Lambda^m g is polynomial and hence smooth.
    Evaluation at the fixed standard top word gives its
    actual exterior-vector realization. All norms are the
    Chapter 1 inner-product norms, not the mass norms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP TensorFamilyUP FamilyUpdate
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness
  ExteriorGrading ExteriorNorm InnerExteriorPositivity FiniteExteriorPowers
  EuclideanHomInnerCharts EuclideanExteriorWordCoefficient
  ContinuousMultilinearUP ContinuousMultilinearSealed
  NormClassHigherUP NormRegularity NormOpenDomainLaws
  NormClassInfinityMultilinearDiagonal NormDiagonalMultilinearDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ExteriorMap.
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

(** Source for [euclidean_exterior_word_map]: Q evaluated
    at the standard unit top word, Federer 3.2.28(2),
    p. 264. This definition is the actual exterior word
    of the frame images, including the literal empty word. *)
Definition euclidean_exterior_word_map (g:X):Y:=
  euclidean_exterior_word_coefficient [ffun _: 'I_m=>g].

(** Source for [euclidean_exterior_word_smooth]: the
    smooth polynomial Q in Federer 3.2.28(2), p. 264,
    by the proved continuous multilinear diagonal theorem
    of 3.1.11, p. 221. No differentiability premise is assumed. *)
Theorem euclidean_exterior_word_smooth:
  norm_class_all_orders hNX hNY (fun _=>True) euclidean_exterior_word_map.
Proof.
exact:(@norm_class_infinity_bounded_multilinear_diagonal R X Y NX NY hNX hNY
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY)
  (fun _=>True) (fun x _=>@norm_full_domain_interior R X NX x) m
  (@euclidean_exterior_word_coefficient R m n)
  (@euclidean_exterior_word_coefficient_bounded R m n h2)).
Qed.

(** Source for [euclidean_exterior_word_differential_exists]:
    the differential DQ(g) used in Federer 3.2.28(2),
    p. 264, is the sum of words obtained by replacing
    one frame image g(e_i) by h(e_i). This supporting
    explicit formula follows from 3.1.1(4) and 3.1.11,
    pp. 210 and 220, and includes degree zero. *)
Theorem euclidean_exterior_word_differential_exists (g:X):
  exists L:Hom X Y,
    has_norm_differential NX NY (fun _=>True) euclidean_exterior_word_map g L /\
    forall h,L h=\sum_(i<m) euclidean_exterior_word_coefficient
      (family_with (i:=i) [ffun _: 'I_m=>g] h).
Proof.
exact:(@norm_diagonal_multilinear_differential R m X Y NX NY hNX hNY
  (@euclidean_exterior_word_coefficient R m n)
  (@euclidean_exterior_word_coefficient_bounded R m n h2) g).
Qed.
End ExteriorMap.
