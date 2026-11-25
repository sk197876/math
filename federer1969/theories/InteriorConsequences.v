(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDuality.
From Federer Require Import InteriorOneDegree InteriorNilpotency InteriorAuxiliaryDecomposition SubspaceSums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.3: the two consequences and the direct sum, in the
    order of the book. All statements concern the actual A^j V. *)
Section Consequences.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable v : V.
Variable alpha : A_m V K^o 1.
Hypothesis hv : one_hom alpha v = 1.
Local Notation E := (exterior_space V).
Local Notation R := (v_interior v).
Local Notation W := (wedge_alpha h2 alpha).
(** Source for [wedge_alpha_square]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma wedge_alpha_square n (phi : A_m V K^o n) : W (W phi) = 0.
Proof.
apply: form_hom_ext => x; rewrite wedge_alpha_homE wedge_alpha_hom form_hom_zeroE.
exact (congr1 (fun f : Hom E K^o => f x)
  (@wedge_alpha_square_hom K h2 V alpha (form_homogeneous phi))).
Qed.
(** Source for [v_interior_square]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma v_interior_square n (gamma : A_m V K^o n.+2) : R (R gamma) = 0.
Proof.
apply: form_hom_ext => x; rewrite !v_interior_homE form_hom_zeroE
  -wedge_assoc exterior_generator_square (bil0r (wedge_bilinear V)); exact: linear0.
Qed.
(** Source for [wedge_alpha_zero_iff]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem wedge_alpha_zero_iff n (phi : A_m V K^o n.+1) :
  W phi = 0 <-> exists beta : A_m V K^o n, phi = W beta.
Proof.
split=> [hz|[beta ->]]; last exact: wedge_alpha_square.
exists (R phi).
have h := @FedererInteriorDecomposition.interior_decomposition K h2 V v alpha hv n phi.
by rewrite hz linear0 add0r in h.
Qed.
(** Source for [v_interior_zero_iff]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem v_interior_zero_iff n (phi : A_m V K^o n.+1) :
  R phi = 0 <-> exists gamma : A_m V K^o n.+2, phi = R gamma.
Proof.
split=> [hz|[gamma ->]]; last exact: v_interior_square.
exists (W phi).
have h := @FedererInteriorDecomposition.interior_decomposition K h2 V v alpha hv n phi.
by rewrite hz linear0 addr0 in h.
Qed.
(** Source for [exterior_summand]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Definition or construction used to formalise this passage. *)
Definition exterior_summand n : subspace (A_m V K^o n.+1) :=
  range_subspace (GRing.Linear.clone _ _ _ _ (@wedge_alpha K h2 V alpha n) _).
(** Source for [interior_summand]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Definition or construction used to formalise this passage. *)
Definition interior_summand n : subspace (A_m V K^o n.+1) :=
  range_subspace (GRing.Linear.clone _ _ _ _ (@v_interior K V v n.+1) _).
(** Source for [interior_direct_sum]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem interior_direct_sum n : is_internal_direct_sum (exterior_summand n) (interior_summand n).
Proof.
split.
- move=> phi; exists (W (R phi)), (R (W phi)); split; first by exists (R phi).
  split; first by exists (W phi).
  rewrite addrC; exact: (@FedererInteriorDecomposition.interior_decomposition K h2 V v alpha hv n phi).
- move=> phi hp hq.
  have hw : W phi = 0 := (proj2 (wedge_alpha_zero_iff phi)) hp.
  have hr : R phi = 0 := (proj2 (v_interior_zero_iff phi)) hq.
  have h := @FedererInteriorDecomposition.interior_decomposition K h2 V v alpha hv n phi.
  by rewrite hw hr !linear0 add0r in h.
Qed.
(** Source for [interior_summands_unique]: Federer (1969), 1.5.3, p. 23, two
    equivalences and the following direct-sum display. In words: The kernels
    of the two square-zero operations are the corresponding images, and the
    space of positive-degree forms splits into the two displayed image
    subspaces. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem interior_summands_unique n (p q p' q' : A_m V K^o n.+1) :
  exterior_summand n p -> interior_summand n q ->
  exterior_summand n p' -> interior_summand n q' ->
  p+q=p'+q' -> p=p' /\ q=q'.
Proof. exact: (internal_sum_unique (interior_direct_sum n)). Qed.
End Consequences.
