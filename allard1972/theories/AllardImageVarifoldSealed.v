(** Allard (1972), 3.2(1), printed p. 430, specialised to M = M' = R^n;
    blueprint al:3.2. Opaque choice of the image varifold F_# V: only the
    characteristic property [is_image_varifold] is exposed, under the
    hypotheses that V ∈ V_k(R^n) and that F satisfies
    [is_proper_class_one_immersion]. Later files import
    AllardImageVarifold.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal
  topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates Hom.
From Allard Require Import AllardGrassmann AllardVarifolds AllardImageVarifoldUP
  AllardImageVarifoldConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ImageVarifoldSignature.
(** Source for [value]: the image varifold F_# V of Allard 3.2, p. 430,
    for M = M' = R^n. *)
Parameter value : forall (R : realType) (n k : nat) (F : R_n R n -> R_n R n)
  (DF : R_n R n -> Hom (R_n R n) (R_n R n)),
  (set (grassmann_bundle R n k) -> \bar R) -> set (grassmann_bundle R n k) -> \bar R.
(** Source for [laws]: the characteristic property 3.2(1) of F_# V,
    Allard 3.2, p. 430. *)
Parameter laws : forall (R : realType) (n k : nat) (F : R_n R n -> R_n R n)
  (DF : R_n R n -> Hom (R_n R n) (R_n R n)) (V : set (grassmann_bundle R n k) -> \bar R),
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_image_varifold F DF V (@value R n k F DF V).
End ImageVarifoldSignature.

Module ImageVarifold : ImageVarifoldSignature.
(** Source for [value]: private selection of the measure supplied by
    [image_varifold_exists], Allard 3.2, p. 430. *)
Definition value (R : realType) (n k : nat) (F : R_n R n -> R_n R n)
    (DF : R_n R n -> Hom (R_n R n) (R_n R n)) (V : set (grassmann_bundle R n k) -> \bar R) :
    set (grassmann_bundle R n k) -> \bar R :=
  projT1 (cid (@image_varifold_exists R n k F DF V)).
(** Source for [laws]: the selected measure has the property 3.2(1),
    Allard 3.2, p. 430. *)
Lemma laws (R : realType) (n k : nat) (F : R_n R n -> R_n R n)
    (DF : R_n R n -> Hom (R_n R n) (R_n R n)) (V : set (grassmann_bundle R n k) -> \bar R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_image_varifold F DF V (@value R n k F DF V).
Proof. exact: projT2 (cid (@image_varifold_exists R n k F DF V)). Qed.
End ImageVarifold.
