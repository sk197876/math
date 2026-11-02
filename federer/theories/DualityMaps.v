(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: D_p and D^p are defined using only the top-degree
    covector omega_mu and vector e_mu. They do not take a whole basis as
    an argument. D_upper is the source identifier for the superscript D^p. *)
Section DualityMaps.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable omega_mu : A_m V K^o n.
(** Source for [D_p]: Federer (1969), 1.5.2, p. 22, last paragraph,
    top-degree products and D_p and D^p. In words: Contraction with dual
    top-degree basis elements gives the two duality isomorphisms; D_p and
    D^(n-p) are inverse, and depend only on those top-degree elements.
    Definition or construction used to formalise this passage. *)
Definition D_p p (hp : (p <= n)%N) (xi : exterior_power V p) : A_m V K^o (n-p) :=
  right_interior hp xi omega_mu.
(** Source for [D_p_linear]: Federer (1969), 1.5.2, p. 22, last paragraph,
    top-degree products and D_p and D^p. In words: Contraction with dual
    top-degree basis elements gives the two duality isomorphisms; D_p and
    D^(n-p) are inverse, and depend only on those top-degree elements.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma D_p_linear p hp : linear (@D_p p hp).
Proof. exact: (proj1 (@right_interior_bilinear K V K^o p n hp)). Qed.
HB.instance Definition _ p hp := GRing.isLinear.Build K (exterior_power V p) (A_m V K^o (n-p))
  *:%R (@D_p p hp) (@D_p_linear p hp).
(** Source for [D_pE]: Federer (1969), 1.5.2, p. 22, last paragraph,
    top-degree products and D_p and D^p. In words: Contraction with dual
    top-degree basis elements gives the two duality isomorphisms; D_p and
    D^(n-p) are inverse, and depend only on those top-degree elements.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma D_pE p hp xi zeta :
  form_homogeneous (@D_p p hp xi) zeta = form_homogeneous omega_mu (wedge zeta (component_val xi)).
Proof. exact: right_interior_homogeneousE. Qed.
Hypothesis h2 : (1+1 : K) != 0.
Variable e_mu : exterior_power V n.
(** Source for [D_upper]: Federer (1969), 1.5.2, p. 22, last paragraph,
    top-degree products and D_p and D^p. In words: Contraction with dual
    top-degree basis elements gives the two duality isomorphisms; D_p and
    D^(n-p) are inverse, and depend only on those top-degree elements.
    Definition or construction used to formalise this passage. *)
Definition D_upper p (hp : (p <= n)%N) (phi : A_m V K^o p) : exterior_power V (n-p) :=
  left_interior h2 hp e_mu phi.
(** Source for [D_upper_linear]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma D_upper_linear p hp : linear (@D_upper p hp).
Proof. exact: (proj2 (@left_interior_bilinear K h2 V p n hp)). Qed.
HB.instance Definition _ p hp := GRing.isLinear.Build K (A_m V K^o p) (exterior_power V (n-p))
  *:%R (@D_upper p hp) (@D_upper_linear p hp).
(** Source for [D_upperE]: Federer (1969), 1.5.2, p. 22, last paragraph,
    top-degree products and D_p and D^p. In words: Contraction with dual
    top-degree basis elements gives the two duality isomorphisms; D_p and
    D^(n-p) are inverse, and depend only on those top-degree elements.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma D_upperE p hp phi : component_val (@D_upper p hp phi) =
  left_interior_hom h2 (component_val e_mu) (form_homogeneous phi).
Proof. by []. Qed.
End DualityMaps.

(** Federer 1.5.2: changing the basis without changing the two dual
    top-degree vectors cannot change either duality map. *)
(** Source for [D_p_top_dependence]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma D_p_top_dependence (K : fieldType) (V : lmodType K) n p (hp : (p <= n)%N)
  (omega_mu omega_mu' : A_m V K^o n) : omega_mu = omega_mu' ->
  @D_p K V n omega_mu p hp = @D_p K V n omega_mu' p hp.
Proof. by move=> ->. Qed.
(** Source for [D_upper_top_dependence]: Federer (1969), 1.5.2, p. 22, last
    paragraph, top-degree products and D_p and D^p. In words: Contraction
    with dual top-degree basis elements gives the two duality isomorphisms;
    D_p and D^(n-p) are inverse, and depend only on those top-degree
    elements. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma D_upper_top_dependence (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n p (hp : (p <= n)%N) (e_mu e_mu' : exterior_power V n) :
  e_mu = e_mu' -> @D_upper K V n h2 e_mu p hp = @D_upper K V n h2 e_mu' p hp.
Proof. by move=> ->. Qed.

(** Federer 1.5.2: the diagonal characteristic formula also evaluates
    the output against forms written with a different, equal degree index. *)
(** Source for [left_interior_full_evaluation]: Federer (1969), 1.5.2, p.
    22, last paragraph, top-degree products and D_p and D^p. In words:
    Contraction with dual top-degree basis elements gives the two duality
    isomorphisms; D_p and D^(n-p) are inverse, and depend only on those
    top-degree elements. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma left_interior_full_evaluation (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) p q r (hpq : (p <= q)%N) (zeta : exterior_power V q)
  (a : A_m V K^o p) (b : A_m V K^o r) :
  form_include b (component_val (left_interior h2 hpq zeta a)) =
    alternating_wedge h2 (scalar_bilinear K) (form_include a) (form_include b) (component_val zeta).
Proof. rewrite left_interiorE; exact: left_interior_diagram. Qed.
