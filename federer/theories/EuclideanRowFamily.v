(** Expanded coordinate support for Federer (1969), 3.2.45,
    p. 279: independent scalar-row laws specify the linear maps
    used while changing one projection row at a time. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct CoordinateProjection
  InnerProductUP InnerProductLaws Bilinear Adjoint AdjointUP AdjointLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_euclidean_row_family]: independent coordinate
    laws for a helper in the exponent continuity argument of
    Federer 3.2.45, p. 279. Each prescribed source vector is
    the Riesz vector of the corresponding scalar row, as in 1.7.4,
    p. 30. Existence is proved below; the laws select no map. *)
Definition is_euclidean_row_family (R : realType) n m
    (v : 'I_m -> R_n R n) (F : {linear R_n R n -> R_n R m}) : Prop :=
  forall x i, F x i = euclidean_inner_product x (v i).

(** Source for [euclidean_row_family_exists]: existence for the
    preceding independent row laws, supporting Federer 3.2.45,
    p. 279, by the finite coordinate and inner-product laws of
    1.7.1, p. 28. The coordinate construction serves solely as
    an existence proof. The zero row family is retained. *)
Lemma euclidean_row_family_exists (R : realType) n m (v : 'I_m -> R_n R n) :
  exists F, is_euclidean_row_family v F.
Proof.
pose f (x : R_n R n) : R_n R m := [ffun i => euclidean_inner_product x (v i)].
have hLinear : linear f.
  move=> c x y; apply/ffunP=> i.
  by rewrite /f !ffunE (bilDl (inner_bilinear (@euclidean_inner_productP R n)))
    (bilZl (inner_bilinear (@euclidean_inner_productP R n))).
pose H := @HomMap R (R_n R n) (R_n R m) f (introT (asboolP _) hLinear).
exists (hom_as_linear H)=> x i.
by rewrite hom_as_linearE /H /= /f ffunE.
Qed.

(** Source for [euclidean_row_family_adjoint]: the prescribed
    rows equal the actual adjoint images of the standard basis,
    by Federer 1.7.4, p. 30; supporting 3.2.45, p. 279.
    This connects the independent row laws to the earlier normal
    Jacobian and its Hadamard bound without opening a seal. *)
Lemma euclidean_row_family_adjoint (R : realType) n m
    (v : 'I_m -> R_n R n) (F : {linear R_n R n -> R_n R m}) :
  is_euclidean_row_family v F -> forall i,
    inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) F (@coordinate_basis R m i) = v i.
Proof.
move=> hRows i.
have hAdjoint := @inner_adjointP R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n) F.
apply: (inner_vectors_ext (@euclidean_inner_productP R n))=> x.
by rewrite hAdjoint euclidean_inner_basis hRows.
Qed.
