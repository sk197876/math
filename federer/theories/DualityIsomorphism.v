(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorMultiplication.
From Federer Require Import DualityMaps DualityBasis DualityInverse.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: reindexing leaves the homogeneous linear map
    unchanged, including when it occurs as a tensor-map argument. *)
(** Source for [form_reindex_Hom]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma form_reindex_Hom (K : fieldType) (V W : lmodType K) p q
  (h : p=q) (phi : A_m V W p) :
  (form_homogeneous (form_reindex h phi) : Hom (exterior_space V) W) =
    (form_homogeneous phi : Hom (exterior_space V) W).
Proof. apply: hom_ext => x; exact: form_reindexE. Qed.

(** Federer 1.5.2: both cancellation laws and both linear
    isomorphisms, with the equal degree expressions identified. *)
Section Isomorphisms.
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
(** Source for [D_inverseK]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem D_inverseK p hp : cancel (@D_inverse K h2 V n e p hp) (D_p ot hp).
Proof.
move=> phi.
have h := @D_upperK K h2 V n e omega he hdual (n-p) (leq_subr p n) phi.
apply: eq_trans _ h.
apply: pairing_ext => xi.
change (form_homogeneous (D_p ot hp (@D_inverse K h2 V n e p hp phi)) (component_val xi) =
  form_homogeneous (@D_upper_inverse K h2 V n omega (n-p) (leq_subr p n)
    (D_upper h2 et (leq_subr p n) phi)) (component_val xi)).
by rewrite /D_upper_inverse form_reindexE !D_pE /D_inverse exterior_reindexE.
Qed.
(** Source for [D_upper_inverseK]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem D_upper_inverseK p hp :
  cancel (@D_upper_inverse K h2 V n omega p hp) (D_upper h2 et hp).
Proof.
move=> xi.
have h := @D_pK K h2 V n e omega he hdual (n-p) (leq_subr p n) xi.
apply: eq_trans _ h.
apply: val_inj.
change (component_val (D_upper h2 et hp (@D_upper_inverse K h2 V n omega p hp xi)) =
  component_val (@D_inverse K h2 V n e (n-p) (leq_subr p n)
    (D_p ot (leq_subr p n) xi))).
rewrite /D_inverse exterior_reindexE !D_upperE /D_upper_inverse form_reindex_Hom.
by [].
Qed.
(** Source for [D_p_isomorphism]: Federer (1969), 1.5.2, p. 22, inverse and
    basis-dependence assertions in the last paragraph. In words: The duality
    maps in complementary degrees are mutually inverse and depend only on
    the chosen dual top-degree elements. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem D_p_isomorphism (p : nat) (hp : (p <= n)%N) : bijective (D_p ot hp).
Proof. exact: (Bijective (@D_pK K h2 V n e omega he hdual p hp) (@D_inverseK p hp)). Qed.
(** Source for [D_upper_isomorphism]: Federer (1969), 1.5.2, p. 22, inverse
    and basis-dependence assertions in the last paragraph. In words: The
    duality maps in complementary degrees are mutually inverse and depend
    only on the chosen dual top-degree elements. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem D_upper_isomorphism (p : nat) (hp : (p <= n)%N) : bijective (D_upper h2 et hp).
Proof. exact: (Bijective (@D_upperK K h2 V n e omega he hdual p hp) (@D_upper_inverseK p hp)). Qed.
End Isomorphisms.
