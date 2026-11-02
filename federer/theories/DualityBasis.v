(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.
From Federer Require Import DualityMaps TopComplements InteriorSigns
  InteriorBasisFormula InteriorBasisEvaluation CovectorBasisSeparation
  CovectorWords InteriorComplements InteriorIndexRelations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: the identity index mu and the values of D_p and D^p
    on the Grassmann bases. No choice of a new orientation is made. *)
Section DualityBasis.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Local Notation et := (e_lambda e (val (Lambda_top n))).
Local Notation ot := (omega_lambda h2 omega (Lambda_top n)).
(** Source for [top_dual_pair]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma top_dual_pair : pairing et ot = 1.
Proof. by rewrite (pairing_e_omega h2 hdual) eqxx. Qed.
(** Source for [D_p_basis]: Federer (1969), 1.5.2, p. 22, last paragraph,
    top-degree products and D_p and D^p. In words: Contraction with dual
    top-degree basis elements gives the two duality isomorphisms; D_p and
    D^(n-p) are inverse, and depend only on those top-degree elements.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma D_p_basis p (hp : (p <= n)%N) (lambda : Lambda n p) :
  D_p ot hp (e_lambda e (val lambda)) =
    (-1 : K)^+(FedererInteriorSigns.M lambda (top_complement lambda)) *:
      omega_lambda h2 omega (top_complement lambda).
Proof.
exact: (@right_interior_basis K h2 V n p n e omega he hdual hp lambda
  (Lambda_top n) (Lambda_subset_top lambda)).
Qed.
(** Source for [D_upper_basis]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma D_upper_basis p (hp : (p <= n)%N) (lambda : Lambda n p) :
  D_upper h2 et hp (omega_lambda h2 omega lambda) =
    (-1 : K)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *:
      e_lambda e (val (top_complement lambda)).
Proof.
exact: (@left_interior_basis K h2 V n p n e omega he hdual hp lambda
  (Lambda_top n) (Lambda_subset_top lambda)).
Qed.
(** Source for [D_inverse]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Definition or construction used to
    formalise this passage. *)
Definition D_inverse p (hp : (p <= n)%N) (phi : A_m V K^o (n-p)) : exterior_power V p :=
  exterior_reindex (subKn hp) (D_upper h2 et (leq_subr p n) phi).
(** Source for [D_inverse_linear]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma D_inverse_linear p hp : linear (@D_inverse p hp).
Proof. by move=> a phi psi; rewrite /D_inverse !linearP. Qed.
HB.instance Definition _ p hp := GRing.isLinear.Build K (A_m V K^o (n-p)) (exterior_power V p)
  *:%R (@D_inverse p hp) (@D_inverse_linear p hp).
(** Source for [D_inverse_evaluation]: Federer (1969), 1.5.2, p. 22, inverse
    and basis-dependence assertions in the last paragraph. In words: The
    duality maps in complementary degrees are mutually inverse and depend
    only on the chosen dual top-degree elements. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma D_inverse_evaluation p hp phi (beta : A_m V K^o p) :
  pairing (@D_inverse p hp phi) beta =
    alternating_wedge h2 (scalar_bilinear K) (form_include phi) (form_include beta) (component_val et).
Proof.
change (form_include beta (component_val (@D_inverse p hp phi)) =
  alternating_wedge h2 (scalar_bilinear K) (form_include phi) (form_include beta) (component_val et)).
rewrite /D_inverse exterior_reindexE; exact: left_interior_full_evaluation.
Qed.
(** Source for [D_inverse_basisK]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma D_inverse_basisK p hp (lambda : Lambda n p) :
  @D_inverse p hp (D_p ot hp (e_lambda e (val lambda))) = e_lambda e (val lambda).
Proof.
rewrite (D_p_basis hp lambda) linearZ.
apply: (@pairing_covector_basis_ext K h2 V n p e omega he hdual) => mu.
rewrite (bilZl (@pairing_bilinear K V K^o p)) D_inverse_evaluation
  -!covector_word_Lambda covector_word_product e_lambdaE.
have hs : size (val (top_complement lambda) ++ val mu) = n.
  by rewrite size_cat !size_tuple subnK.
rewrite (@covector_word_pairing_seq K h2 V n e omega hdual n
  (val (top_complement lambda) ++ val mu) (Lambda_top n) hs) top_complement_shared_left
  (pairing_e_omega h2 hdual).
case hm: (mu == lambda).
- move/eqP: hm => ->; rewrite -FedererInteriorSigns.M_inversions.
  change ((-1 : K)^+(FedererInteriorSigns.M lambda (top_complement lambda)) *
    (-1 : K)^+(FedererInteriorSigns.M lambda (top_complement lambda)) = 1).
  by rewrite -exprMn mulrNN mul1r expr1n.
- exact: scaler0.
Qed.
(** Source for [D_pK]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem D_pK p hp : cancel (D_p ot hp) (@D_inverse p hp).
Proof.
apply: (@basis_linear_ext K (Choice.clone (Lambda n p) _) (exterior_power V p)
  (@finite_e_lambda K n V e p) (finite_e_lambda_basis he h2 p) (exterior_power V p)
  (linear_comp (GRing.Linear.clone _ _ _ _ (@D_inverse p hp) _) (GRing.Linear.clone _ _ _ _ (D_p ot hp) _))
  (linear_id (exterior_power V p))).
exact: D_inverse_basisK.
Qed.
End DualityBasis.
