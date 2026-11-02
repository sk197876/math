(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3: write j=n+1 and identify n+1-1 with n.
    These maps are the interior and exterior multiplications of 1.5.1;
    the degree identifications change neither forms nor multivectors. *)
(** Source for [successor_sub_one]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma successor_sub_one n : (n.+1 - 1)%N = n.
Proof. by rewrite subn1. Qed.
Section Operations.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable v : V.
Variable alpha : A_m V K^o 1.
Local Notation E := (exterior_space V).
Local Notation ev := (exterior_generator v).
Local Notation v1 := (exterior_first_inclusion V v).
(** Source for [first_inclusion_val]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma first_inclusion_val : component_val v1 = ev.
Proof. exact: exterior_generator_homogeneous. Qed.
(** Source for [v_interior]: Federer (1969), 1.5.3, p. 23, first display and
    auxiliary decomposition in its proof. In words: If a one-covector alpha
    takes value one on v, every positive-degree form is v contracted into
    its product with alpha plus its contraction by v multiplied by alpha.
    Definition or construction used to formalise this passage. *)
Definition v_interior n (phi : A_m V K^o n.+1) : A_m V K^o n :=
  form_reindex (successor_sub_one n) (@right_interior K V K^o 1 n.+1 (leq0n n) v1 phi).
(** Source for [wedge_alpha]: Federer (1969), 1.5.3, p. 23, first display
    and auxiliary decomposition in its proof. In words: If a one-covector
    alpha takes value one on v, every positive-degree form is v contracted
    into its product with alpha plus its contraction by v multiplied by
    alpha. Definition or construction used to formalise this passage. *)
Definition wedge_alpha n (phi : A_m V K^o n) : A_m V K^o n.+1 :=
  form_reindex (addn1 n) (form_wedge h2 (scalar_bilinear K) phi alpha).
(** Source for [v_interior_homE]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma v_interior_homE n (phi : A_m V K^o n.+1) x :
  form_homogeneous (v_interior phi) x = form_homogeneous phi (wedge x ev).
Proof. by rewrite /v_interior form_reindexE right_interior_homogeneousE first_inclusion_val. Qed.
(** Source for [wedge_alpha_homE]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma wedge_alpha_homE n (phi : A_m V K^o n) x :
  form_homogeneous (wedge_alpha phi) x =
    convolution (scalar_bilinear K) (Psi h2 V) (form_homogeneous phi) (form_homogeneous alpha) x.
Proof. by rewrite /wedge_alpha form_reindexE form_wedge_hom. Qed.
(** Source for [v_interior_hom]: Federer (1969), 1.5.3, p. 23, first display
    and auxiliary decomposition in its proof. In words: If a one-covector
    alpha takes value one on v, every positive-degree form is v contracted
    into its product with alpha plus its contraction by v multiplied by
    alpha. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma v_interior_hom n (phi : A_m V K^o n.+1) :
  (form_homogeneous (v_interior phi) : Hom E K^o) =
    right_interior_hom ev (form_homogeneous phi).
Proof. apply: hom_ext => x; exact: v_interior_homE. Qed.
(** Source for [wedge_alpha_hom]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma wedge_alpha_hom n (phi : A_m V K^o n) :
  (form_homogeneous (wedge_alpha phi) : Hom E K^o) =
    convolution (scalar_bilinear K) (Psi h2 V) (form_homogeneous phi) (form_homogeneous alpha).
Proof. apply: hom_ext => x; exact: wedge_alpha_homE. Qed.
(** Source for [v_interior_linear]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma v_interior_linear n : linear (@v_interior n).
Proof.
move=> c phi psi; rewrite /v_interior (proj2 (@right_interior_bilinear K V K^o 1 n.+1 (leq0n n))).
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build K (A_m V K^o n.+1)
  (A_m V K^o n) *:%R (@v_interior n) (@v_interior_linear n).
(** Source for [wedge_alpha_linear]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma wedge_alpha_linear n : linear (@wedge_alpha n).
Proof.
move=> c phi psi; rewrite /wedge_alpha (proj1 (@form_wedge_bilinear K h2 V K^o _ (scalar_bilinear K) n 1)).
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build K (A_m V K^o n)
  (A_m V K^o n.+1) *:%R (@wedge_alpha n) (@wedge_alpha_linear n).

(** Federer 1.5.3, the auxiliary condition v interior beta=0 when j=1.
    For a zero-form, the homogeneous linear map vanishes after right
    multiplication by v. This proves the implicit degree-zero convention. *)
(** Source for [v_interior_zero_degree]: Federer (1969), 1.5.3, p. 23, first
    display and auxiliary decomposition in its proof. In words: If a
    one-covector alpha takes value one on v, every positive-degree form is v
    contracted into its product with alpha plus its contraction by v
    multiplied by alpha. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma v_interior_zero_degree (beta : A_m V K^o 0) :
  right_interior_hom ev (form_homogeneous beta) = 0.
Proof.
apply: hom_ext => x; rewrite right_interior_homE hom_zeroE.
elim/(graded_induction (G:=exterior_grading V)): x => [|x y hx hy|n x hx].
- by rewrite (bil0l (wedge_bilinear V)) linear0.
- rewrite (bilDl (wedge_bilinear V)) linearD.
  change (form_homogeneous beta (wedge x ev) + form_homogeneous beta (wedge y ev) = 0).
  by rewrite hx hy add0r.
- have hn : (n+1)%N != 0 by rewrite addn1.
  exact: (hom_m_degree (form_homogeneous beta) hn
    (wedge_graded hx (exterior_generator_homogeneous v))).
Qed.
(** Source for [left_alpha]: Federer (1969), 1.5.3, p. 23, first display and
    auxiliary decomposition in its proof. In words: If a one-covector alpha
    takes value one on v, every positive-degree form is v contracted into
    its product with alpha plus its contraction by v multiplied by alpha.
    Definition or construction used to formalise this passage. *)
Definition left_alpha n (xi : exterior_power V n.+1) : exterior_power V n :=
  exterior_reindex (successor_sub_one n) (@left_interior K h2 V 1 n.+1 (leq0n n) xi alpha).
(** Source for [v_wedge]: Federer (1969), 1.5.3, p. 23, first display and
    auxiliary decomposition in its proof. In words: If a one-covector alpha
    takes value one on v, every positive-degree form is v contracted into
    its product with alpha plus its contraction by v multiplied by alpha.
    Definition or construction used to formalise this passage. *)
Definition v_wedge n (xi : exterior_power V n) : exterior_power V n.+1 :=
  exterior_reindex (add1n n) (exterior_product v1 xi).
(** Source for [left_alphaE]: Federer (1969), 1.5.3, p. 23, first display
    and auxiliary decomposition in its proof. In words: If a one-covector
    alpha takes value one on v, every positive-degree form is v contracted
    into its product with alpha plus its contraction by v multiplied by
    alpha. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma left_alphaE n (xi : exterior_power V n.+1) :
  component_val (left_alpha xi) = left_interior_hom h2 (component_val xi) (form_homogeneous alpha).
Proof. by rewrite /left_alpha exterior_reindexE left_interiorE. Qed.
(** Source for [v_wedgeE]: Federer (1969), 1.5.3, p. 23, first display and
    auxiliary decomposition in its proof. In words: If a one-covector alpha
    takes value one on v, every positive-degree form is v contracted into
    its product with alpha plus its contraction by v multiplied by alpha.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma v_wedgeE n (xi : exterior_power V n) : component_val (v_wedge xi) = wedge ev (component_val xi).
Proof. by rewrite /v_wedge exterior_reindexE exterior_productE first_inclusion_val. Qed.
End Operations.
