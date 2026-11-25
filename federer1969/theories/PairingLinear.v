(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import AlternatingAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3: the two linear evaluation maps supplied by the pairing. *)
Section PairingLinear.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
(** Source for [pairing_right_fun]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Definition or
    construction used to formalise this passage. *)
Definition pairing_right_fun (xi : exterior_power V m) (phi : A_m V K^o m) : K^o := pairing xi phi.
(** Source for [pairing_right_linear]: Federer (1969), 1.4.1, p. 17,
    paragraph extending the evaluation notation. In words: The pairing is
    evaluation of a linear map on an m-vector and has the same value under
    the identifications with forms and homogeneous linear maps. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma pairing_right_linear xi : linear (pairing_right_fun xi).
Proof. exact: (proj2 (@pairing_bilinear K V K^o m)). Qed.
HB.instance Definition _ xi := GRing.isLinear.Build K (A_m V K^o m) K^o *:%R
  (pairing_right_fun xi) (pairing_right_linear xi).
(** Source for [pairing_right]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Definition or
    construction used to formalise this passage. *)
Definition pairing_right xi : {linear A_m V K^o m -> K^o} :=
  GRing.Linear.clone _ _ _ _ (pairing_right_fun xi) _.
(** Source for [pairing_rightE]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma pairing_rightE xi phi : pairing_right xi phi = pairing xi phi.
Proof. by []. Qed.
(** Source for [pairing_left]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Definition or
    construction used to formalise this passage. *)
Definition pairing_left (phi : A_m V K^o m) : {linear exterior_power V m -> K^o} :=
  hom_as_linear (form_to_hom phi).
(** Source for [pairing_leftE]: Federer (1969), 1.4.1, p. 17, paragraph
    extending the evaluation notation. In words: The pairing is evaluation
    of a linear map on an m-vector and has the same value under the
    identifications with forms and homogeneous linear maps. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma pairing_leftE phi xi : pairing_left phi xi = pairing xi phi.
Proof. by []. Qed.
End PairingLinear.
