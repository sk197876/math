(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.6.1, e_1,...,e_k as the initial part of the ambient basis.
    Ordinal i denotes Federer's i+1. *)
Section Initial.
Variables k n : nat.
Variable hkn : k <= n.
(** Source for [initial_tuple]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Definition or construction used to
    formalise this passage. *)
Definition initial_tuple : k.-tuple 'I_n := [tuple widen_ord hkn i | i < k].
(** Source for [initial_sorted]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma initial_sorted : sorted ltn (map val initial_tuple).
Proof.
rewrite /initial_tuple /= -map_comp.
change (sorted ltn [seq val i | i <- enum 'I_k]).
by rewrite val_enum_ord iota_ltn_sorted.
Qed.
(** Source for [Lambda_initial]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Definition or construction used to
    formalise this passage. *)
Definition Lambda_initial : Lambda n k := Sub initial_tuple initial_sorted.
(** Source for [initial_set_mem]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma initial_set_mem (i : 'I_n) : (i \in Lambda_set Lambda_initial) = (i < k).
Proof.
rewrite /Lambda_set inE; change ((i \in [seq widen_ord hkn j | j <- enum 'I_k]) = (i < k)).
apply/mapP/idP.
- move=> [j hj ->]; change (val j < k); exact: ltn_ord.
- move=> hi; exists (Ordinal hi); first exact: mem_enum.
  exact: val_inj.
Qed.
Variable m : nat.
Variable lambda : Lambda n m.
Variable hsub : Lambda_set Lambda_initial \subset Lambda_set lambda.
Local Notation nu := (InteriorComplements.nu hsub).
(** Source for [initial_complement_after]: Federer (1969), 1.6.1, p. 23,
    last paragraph, basis extension and the Grassmann-coordinate argument.
    In words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma initial_complement_after i : i \in Lambda_set nu -> k <= i.
Proof.
rewrite nu_image in_setD initial_set_mem => /andP [hi _].
by rewrite leqNgt.
Qed.
(** Source for [initial_complement_before]: Federer (1969), 1.6.1, p. 23,
    last paragraph, basis extension and the Grassmann-coordinate argument.
    In words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma initial_complement_before i j :
  i \in Lambda_set Lambda_initial -> j \in Lambda_set nu -> i < j.
Proof.
rewrite initial_set_mem => hi hj; exact: leq_trans hi (initial_complement_after hj).
Qed.
(** Source for [initial_complement_N]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma initial_complement_N : FedererInteriorSigns.N Lambda_initial nu = 0.
Proof.
apply/eqP; rewrite /FedererInteriorSigns.N cards_eq0; apply/eqP; apply/setP => [[i j]].
rewrite in_set0 inE /=; apply/negbTE/negP=> /and3P [hi hj hji].
have hij := initial_complement_before hi hj.
by have := ltn_trans hji hij; rewrite ltnn.
Qed.
(** Source for [initial_concatenation_inversions]: Federer (1969), 1.6.1, p.
    23, last paragraph, basis extension and the Grassmann-coordinate
    argument. In words: Extend a basis of the associated space to an ambient
    finite basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma initial_concatenation_inversions : inversions (map val (val Lambda_initial ++ val nu)) = 0.
Proof. by rewrite -FedererInteriorSigns.N_inversions initial_complement_N. Qed.
End Initial.
