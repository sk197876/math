(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import ExteriorBases.
From Federer Require Import TensorAssociator GradedTensorAssociator ExteriorDiagonal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.3, associativity diagram. The two vertical maps are
    algebra homomorphisms and agree on V; the canonical reassociation
    identifies their codomains. Both displayed generator calculations
    are proved before the universal-property argument. *)
Section Coassociativity.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable V : lmodType K.
Local Notation E := (exterior_unital V).
Local Notation T := (unital_graded_tensor E E true).
Local Notation L := (unital_graded_tensor T E true).
Local Notation R := (unital_graded_tensor E T true).
Local Notation D := (Psi h2 V).
Local Notation u := (exterior_unit V).
Local Notation idE := (algebra_id E).

(** Source for [Psi_left]: Federer (1969), 1.3.3, p. 15, associativity
    diagram and following generator calculation. In words: The two iterated
    diagonal maps agree after reassociation, since each sends a vector to
    the sum of its three placements among tensor units. Definition or
    construction used to formalise this passage. *)
Definition Psi_left : algebra_map T L := @unital_tensor_map K E E T E D idE
  (@Psi_graded K h2 V) (fun n x hx => hx) true.
(** Source for [Psi_right]: Federer (1969), 1.3.3, p. 15, associativity
    diagram and following generator calculation. In words: The two iterated
    diagonal maps agree after reassociation, since each sends a vector to
    the sum of its three placements among tensor units. Definition or
    construction used to formalise this passage. *)
Definition Psi_right : algebra_map T R := @unital_tensor_map K E E E T idE D
  (fun n x hx => hx) (@Psi_graded K h2 V) true.

(** Source for [Psi_leftE]: Federer (1969), 1.3.3, p. 15, associativity
    diagram and following generator calculation. In words: The two iterated
    diagonal maps agree after reassociation, since each sends a vector to
    the sum of its three placements among tensor units. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma Psi_leftE v : Psi_left (D (exterior_generator v)) =
  tensor_inj (tensor_inj (exterior_generator v) u) u +
  tensor_inj (tensor_inj u (exterior_generator v)) u +
  tensor_inj (tensor_inj u u) (exterior_generator v).
Proof.
pose z := exterior_generator v.
have hD0 : D u = tensor_inj u u := algebra_map_one D.
have hDz : D z = tensor_inj z u + tensor_inj u z := PsiE h2 v.
have hz : Psi_left (tensor_inj z u) =
    tensor_inj (tensor_inj z u) u + tensor_inj (tensor_inj u z) u.
  apply: eq_trans (@tensor_mapE K E E T E D idE z u) _.
  apply: eq_trans (congr1 (fun x : T => tensor_inj x u) hDz) _.
  exact: tensor_inj_addl.
have hu : Psi_left (tensor_inj u z) = tensor_inj (tensor_inj u u) z.
  apply: eq_trans (@tensor_mapE K E E T E D idE u z) _.
  exact (congr1 (fun x : T => tensor_inj x z) hD0).
apply: eq_trans (congr1 Psi_left hDz) _.
rewrite linearD; exact (congr2 (+%R) hz hu).
Qed.

(** Source for [Psi_rightE]: Federer (1969), 1.3.3, p. 15, associativity
    diagram and following generator calculation. In words: The two iterated
    diagonal maps agree after reassociation, since each sends a vector to
    the sum of its three placements among tensor units. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma Psi_rightE v : Psi_right (D (exterior_generator v)) =
  tensor_inj (exterior_generator v) (tensor_inj u u) +
  (tensor_inj u (tensor_inj (exterior_generator v) u) +
   tensor_inj u (tensor_inj u (exterior_generator v))).
Proof.
pose z := exterior_generator v.
have hD0 : D u = tensor_inj u u := algebra_map_one D.
have hDz : D z = tensor_inj z u + tensor_inj u z := PsiE h2 v.
have hz : Psi_right (tensor_inj z u) = tensor_inj z (tensor_inj u u).
  apply: eq_trans (@tensor_mapE K E E E T idE D z u) _.
  exact (congr1 (fun x : T => tensor_inj z x) hD0).
have hu : Psi_right (tensor_inj u z) =
    tensor_inj u (tensor_inj z u) + tensor_inj u (tensor_inj u z).
  apply: eq_trans (@tensor_mapE K E E E T idE D u z) _.
  apply: eq_trans (congr1 (fun x : T => tensor_inj u x) hDz) _.
  exact: tensor_inj_addr.
apply: eq_trans (congr1 Psi_right hDz) _.
rewrite linearD; exact (congr2 (+%R) hz hu).
Qed.

(** Source for [Psi_coassociative]: Federer (1969), 1.3.3, p. 15,
    associativity diagram and following generator calculation. In words: The
    two iterated diagonal maps agree after reassociation, since each sends a
    vector to the sum of its three placements among tensor units. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem Psi_coassociative x : tensor_associator E E E (Psi_left (D x)) = Psi_right (D x).
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp (unital_tensor_associator E E E true) (algebra_comp Psi_left D))
  (algebra_comp Psi_right D)) x => v.
change (tensor_associator E E E (Psi_left (D (exterior_generator v))) =
  Psi_right (D (exterior_generator v))).
pose z := exterior_generator v.
pose a := tensor_inj (tensor_inj z u) u.
pose b := tensor_inj (tensor_inj u z) u.
pose c := tensor_inj (tensor_inj u u) z.
pose f := tensor_associator E E E.
have hd : f (a+b+c) = (f a+f b)+f c by rewrite !linearD.
have h1 := @tensor_associatorE K E E E z u u.
have h2' := @tensor_associatorE K E E E u z u.
have h3 := @tensor_associatorE K E E E u u z.
apply: eq_trans (congr1 f (@Psi_leftE v)) _.
apply: eq_trans hd _.
apply: eq_trans (congr2 (+%R) (congr2 (+%R) h1 h2') h3) _.
apply: eq_trans (esym (addrA _ _ _)) _.
exact: esym (@Psi_rightE v).
Qed.
End Coassociativity.
