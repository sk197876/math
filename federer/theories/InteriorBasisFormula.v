(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.
From Federer Require Import InteriorComplements InteriorIndexRelations
  InteriorSigns InteriorBasisEvaluation CovectorBasisSeparation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2, first two cases: the precise basis formulae for
    e_lambda interior omega_mu and e_mu interior omega_lambda. *)
Section BasisFormulae.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n p q : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Variable hpq : (p <= q)%N.
Variables (lambda : Lambda n p) (mu : Lambda n q).
(** Source for [right_interior_basis_zero]: Federer (1969), 1.5.2, p. 22,
    the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem right_interior_basis_zero : ~~ (Lambda_set lambda \subset Lambda_set mu) ->
  right_interior hpq (e_lambda e (val lambda)) (omega_lambda h2 omega mu) = 0.
Proof.
move=> hn; apply: (@pairing_basis_ext K h2 V n (q-p) e he) => kappa.
rewrite (right_interior_basis_evaluation h2 hdual) perm_catC
  (negbTE (Lambda_concat_not_subset kappa hn)).
symmetry; exact: (bil0r (@pairing_bilinear K V K^o (q-p))).
Qed.
(** Source for [left_interior_basis_zero]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem left_interior_basis_zero : ~~ (Lambda_set lambda \subset Lambda_set mu) ->
  left_interior h2 hpq (e_lambda e (val mu)) (omega_lambda h2 omega lambda) = 0.
Proof.
move=> hn; apply: (@pairing_covector_basis_ext K h2 V n (q-p) e omega he hdual) => kappa.
rewrite (left_interior_basis_evaluation h2 hdual)
  (negbTE (Lambda_concat_not_subset kappa hn)).
symmetry; exact: (bil0l (@pairing_bilinear K V K^o (q-p))).
Qed.
Variable hsub : Lambda_set lambda \subset Lambda_set mu.
Local Notation nu := (InteriorComplements.nu hsub).
(** Source for [right_interior_basis]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem right_interior_basis :
  right_interior hpq (e_lambda e (val lambda)) (omega_lambda h2 omega mu) =
    (-1 : K)^+(FedererInteriorSigns.M lambda nu) *: omega_lambda h2 omega nu.
Proof.
apply: (@pairing_basis_ext K h2 V n (q-p) e he) => kappa.
rewrite (right_interior_basis_evaluation h2 hdual) perm_catC
  (Lambda_concat_complement hsub) (bilZr (@pairing_bilinear K V K^o (q-p)))
  (pairing_e_omega h2 hdual) (eq_sym nu kappa).
case hk: (kappa == nu).
- move/eqP: hk => ->; rewrite -FedererInteriorSigns.M_inversions.
  change ((-1 : K)^+(FedererInteriorSigns.M lambda nu) =
    (-1 : K)^+(FedererInteriorSigns.M lambda nu) * 1).
  by rewrite mulr1.
- exact: esym (mulr0 _).
Qed.
(** Source for [left_interior_basis]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem left_interior_basis :
  left_interior h2 hpq (e_lambda e (val mu)) (omega_lambda h2 omega lambda) =
    (-1 : K)^+(FedererInteriorSigns.N lambda nu) *: e_lambda e (val nu).
Proof.
apply: (@pairing_covector_basis_ext K h2 V n (q-p) e omega he hdual) => kappa.
rewrite (left_interior_basis_evaluation h2 hdual)
  (Lambda_concat_complement hsub) (bilZl (@pairing_bilinear K V K^o (q-p)))
  (pairing_e_omega h2 hdual).
case hk: (kappa == nu).
- move/eqP: hk => ->; rewrite -FedererInteriorSigns.N_inversions.
  change ((-1 : K)^+(FedererInteriorSigns.N lambda nu) =
    (-1 : K)^+(FedererInteriorSigns.N lambda nu) * 1).
  by rewrite mulr1.
- exact: esym (mulr0 _).
Qed.
(** Source for [interior_sign_sum]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem interior_sign_sum :
  (FedererInteriorSigns.M lambda nu + FedererInteriorSigns.N lambda nu = p*(q-p))%N.
Proof. apply: FedererInteriorSigns.M_add_N; exact: nu_disjoint. Qed.
End BasisFormulae.
