(** Federer (1969), 3.2.28(2), printed p. 264:
    realizing Q by evaluation on the standard unit top word.
    These are exact algebraic identities for the already
    sealed exterior power, before any manifold restriction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom FamilyUpdate TensorFamilyUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorAlgebra ExteriorGrading ExteriorMaps ExteriorMapNormContinuity
  FiniteExteriorPowers EuclideanExteriorWordCoefficient EuclideanExteriorWordSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_exterior_word_mapE]: evaluating
    Lambda^m g on the standard top word is the exterior
    product of its frame images, 1.3.2, p. 14, as used
    to identify the image of Q in Federer 3.2.28(2), p. 264. *)
Lemma euclidean_exterior_word_mapE (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  euclidean_exterior_word_map g=
    exterior_power_map (hom_as_linear g) m
      (e_lambda (@coordinate_basis R m) (ord_tuple m)).
Proof.
rewrite exterior_power_map_e_lambda /euclidean_exterior_word_map
  /euclidean_exterior_word_coefficient.
have he:(fun i:'I_m=>[ffun _:'I_m=>g] i (@coordinate_basis R m i))=
    hom_as_linear g \o (@coordinate_basis R m).
  apply:funext=>i; by rewrite ffunE.
by rewrite he.
Qed.

(** Source for [euclidean_exterior_word_replacementE]: each
    summand in DQ(g) replaces precisely one g(e_i) by h(e_i).
    Supporting the differential computation in Federer 3.2.28(2),
    p. 264, through the multilinearity of 1.4.1, p. 17. *)
Lemma euclidean_exterior_word_replacementE (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)) (i:'I_m):
  euclidean_exterior_word_coefficient
    (family_with (i:=i) [ffun _:'I_m=>g] h)=
  e_lambda (family_with (i:=i) [ffun j=>g (@coordinate_basis R m j)]
    (h (@coordinate_basis R m i))) (ord_tuple m).
Proof.
rewrite /euclidean_exterior_word_coefficient.
have he:(fun j:'I_m=>family_with (i:=i) [ffun _:'I_m=>g] h j
      (@coordinate_basis R m j))=
    (fun j=>family_with (i:=i) [ffun j=>g (@coordinate_basis R m j)]
      (h (@coordinate_basis R m i)) j).
  apply:funext=>j; case:(eqVneq i j)=>[<-|hij].
  - by rewrite !family_with_in.
  - by rewrite !family_with_out // !ffunE.
by rewrite he.
Qed.
