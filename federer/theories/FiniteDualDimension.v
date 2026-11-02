(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingAlgebra.
From Federer Require Import FiniteIndependence FiniteBasisCriterion Biorthogonal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3, dimension argument: Hom(E,R) has the same finite
    dimension as E. The coordinate functionals of a basis constitute
    its dual basis. This dimension calculation precedes the basis
    assertion about the particular products omega_lambda. *)
Section FiniteDual.
Variable K : fieldType.
Variable I : finType.
Variable V : lmodType K.
Variable e : I -> V.
Hypothesis he : is_basis e.
(** Source for [hom_evaluate]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Definition or
    construction used to formalise this passage. *)
Definition hom_evaluate (v : V) (f : Hom V K^o) : K^o := f v.
(** Source for [hom_evaluate_linear]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma hom_evaluate_linear v : linear (hom_evaluate v).
Proof. exact: hom_eval_linear. Qed.
HB.instance Definition _ v := GRing.isLinear.Build K (Hom V K^o) K^o *:%R
  (hom_evaluate v) (hom_evaluate_linear v).
(** Source for [dual_basis]: Federer (1969), 1.1.4, p. 11, final paragraph,
    the dual-basis conditions. In words: The dual basis consists of linear
    functions taking value one on the corresponding basis vector and zero on
    the other basis vectors. Definition or construction used to formalise
    this passage. The local LaTeX erratum (May 1987), p. 1, entry for book
    p. 11 line 8, corrects the scalar-field typography in Hom(V,R). *)
Definition dual_basis (i : I) : Hom V K^o :=
  hom_of_linear (linear_comp (GRing.Linear.clone _ _ _ _ (free_eval i) _) (basis_coordinates he)).
(** Source for [dual_basisE]: Federer (1969), 1.1.4, p. 11, final paragraph,
    the dual-basis conditions. In words: The dual basis consists of linear
    functions taking value one on the corresponding basis vector and zero on
    the other basis vectors. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum (May 1987), p. 1,
    entry for book p. 11 line 8, corrects the scalar-field typography in
    Hom(V,R). *)
Lemma dual_basisE i j : dual_basis i (e j) = if j == i then 1 else 0.
Proof. change (basis_coordinates he (e j) i = if j == i then 1 else 0); by rewrite basis_coordinatesE deltaE eq_sym. Qed.
(** Source for [dual_sum_evaluate]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma dual_sum_evaluate (c : I -> K) j : (\sum_i c i *: dual_basis i) (e j) = c j.
Proof.
pose f i := hom_of_linear (GRing.Linear.clone _ _ _ _ (hom_evaluate (e i)) _).
have hf a b : f a (dual_basis b) = if a == b then 1 else 0.
  exact: dual_basisE.
exact (@biorthogonal_sum K (Hom V K^o) I f dual_basis hf c j).
Qed.
(** Source for [dual_basis_independent]: Federer (1969), 1.1.4, p. 11, final
    paragraph, the dual-basis conditions. In words: The dual basis consists
    of linear functions taking value one on the corresponding basis vector
    and zero on the other basis vectors. Supporting lemma for this passage;
    not separately stated in the book. The local LaTeX erratum (May 1987),
    p. 1, entry for book p. 11 line 8, corrects the scalar-field typography
    in Hom(V,R). *)
Lemma dual_basis_independent : finite_independent dual_basis.
Proof.
apply: (@finite_independent_separating K I (Hom V K^o) dual_basis
  (fun i => GRing.Linear.clone _ _ _ _ (hom_evaluate (e i)) _)) => i j.
exact: dual_basisE.
Qed.
(** Source for [dual_basisP]: Federer (1969), 1.1.4, p. 11, final paragraph,
    the dual-basis conditions. In words: The dual basis consists of linear
    functions taking value one on the corresponding basis vector and zero on
    the other basis vectors. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum (May 1987), p. 1,
    entry for book p. 11 line 8, corrects the scalar-field typography in
    Hom(V,R). *)
Theorem dual_basisP : is_basis dual_basis.
Proof.
apply: finite_basis_criterion dual_basis_independent _ => f.
exists (fun i => (f (e i) : K)); apply: hom_ext => v.
apply: (basis_linear_ext he (hom_as_linear f)
  (hom_as_linear (\sum_i (f (e i) : K) *: dual_basis i))) v => i.
exact (esym (dual_sum_evaluate (fun j => (f (e j) : K)) i)).
Qed.
(** Source for [finite_dual_space]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Definition or
    construction used to formalise this passage. *)
Definition finite_dual_space : vectType K := finite_basis_vect dual_basisP.
(** Source for [finite_dual_dimension]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem finite_dual_dimension : dim finite_dual_space = #|I|.
Proof. exact: finite_basis_dimension. Qed.
End FiniteDual.

(** Federer 1.4.3: apply the 1.4.1 isomorphism A^m V = Hom(wedge^m V,R),
    then the dimension formula of 1.3.2. *)
Section FormDimension.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable I : finType.
Variable b : I -> exterior_power V m.
Hypothesis hb : is_basis b.
(** Source for [alternating_coordinate_basis]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Definition or
    construction used to formalise this passage. *)
Definition alternating_coordinate_basis i : A_m V K^o m := hom_to_form (dual_basis hb i).
(** Source for [alternating_coordinate_basisP]: Federer (1969), 1.4.3, p.
    19, finite-dimensional basis and dimension paragraph. In words: The
    products of dual basic covectors form the dual basis of the m-th
    exterior power; both degree-m spaces have dimension binomial(n,m).
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma alternating_coordinate_basisP : is_basis alternating_coordinate_basis.
Proof.
exact (@basis_transport K (Choice.clone I _) (Hom (exterior_power V m) K^o) (A_m V K^o m)
  (dual_basis hb) (GRing.Linear.clone _ _ _ _ (@hom_to_form K V K^o m) _)
  (GRing.Linear.clone _ _ _ _ (@form_to_hom K V K^o m) _)
  (@hom_to_formK K V K^o m) (@form_to_homK K V K^o m) (dual_basisP hb)).
Qed.
End FormDimension.
Section PowerDimension.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
(** Source for [finite_form_power]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Definition or
    construction used to formalise this passage. *)
Definition finite_form_power m : vectType K :=
  finite_basis_vect (alternating_coordinate_basisP (finite_e_lambda_basis he h2 m)).
(** Source for [form_power_dimension]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem form_power_dimension m : dim (finite_form_power m) = 'C(n,m).
Proof. rewrite /finite_form_power finite_basis_dimension; exact: card_Lambda. Qed.
(** Source for [form_exterior_dimension]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem form_exterior_dimension m : dim (finite_form_power m) = dim (finite_exterior_power h2 he m).
Proof. by rewrite form_power_dimension exterior_power_dimension. Qed.
End PowerDimension.
