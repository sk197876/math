(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import GrassmannTrace.
From Federer Require Import CrossingCounts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.5.2: retain the names M and N for the two pair counts.
    The second index here is the complementary index nu in the book. *)
Module FedererInteriorSigns.
Section Counts.
Variables n p q : nat.
Variable lambda : Lambda n p.
Variable nu : Lambda n q.
(** Source for [M]: Federer (1969), 1.5.2, p. 22, the two inclusion cases
    and the definitions of M and N. In words: A basis interior product
    vanishes unless the contracted index set is contained in the other;
    otherwise it is the complementary basis product with the appropriate
    crossing-count sign. Definition or construction used to formalise this
    passage. *)
Definition M := #|[set ij : ('I_n*'I_n)%type |
  [&& ij.1 \in Lambda_set lambda, ij.2 \in Lambda_set nu & ij.1 < ij.2]]|.
(** Source for [N]: Federer (1969), 1.5.2, p. 22, the two inclusion cases
    and the definitions of M and N. In words: A basis interior product
    vanishes unless the contracted index set is contained in the other;
    otherwise it is the complementary basis product with the appropriate
    crossing-count sign. Definition or construction used to formalise this
    passage. *)
Definition N := #|[set ij : ('I_n*'I_n)%type |
  [&& ij.1 \in Lambda_set lambda, ij.2 \in Lambda_set nu & ij.2 < ij.1]]|.
(** Source for [N_inversions]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma N_inversions : N = inversions (map val (val lambda ++ val nu)).
Proof. symmetry; exact: Lambda_concat_inversions. Qed.
(** Source for [M_inversions]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma M_inversions : M = inversions (map val (val nu ++ val lambda)).
Proof.
rewrite Lambda_concat_inversions /M.
pose swap (ij : ('I_n*'I_n)%type) := (ij.2,ij.1).
have hswap : involutive swap by move=> [i j].
rewrite -(@card_preimset _ swap
  [set ij : ('I_n*'I_n)%type |
    [&& ij.1 \in Lambda_set nu, ij.2 \in Lambda_set lambda & ij.2 < ij.1]] (can_inj hswap)).
apply: eq_card => [[i j]].
by rewrite /swap !inE andbCA.
Qed.
(** Source for [M_add_N]: Federer (1969), 1.5.2, p. 22, the two inclusion
    cases and the definitions of M and N. In words: A basis interior product
    vanishes unless the contracted index set is contained in the other;
    otherwise it is the complementary basis product with the appropriate
    crossing-count sign. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem M_add_N : uniq (val lambda ++ val nu) -> M + N = p*q.
Proof.
move=> hu.
pose S := [set ij : ('I_n*'I_n)%type |
  [&& ij.1 \in Lambda_set lambda, ij.2 \in Lambda_set nu & ij.1 < ij.2]].
pose T := [set ij : ('I_n*'I_n)%type |
  [&& ij.1 \in Lambda_set lambda, ij.2 \in Lambda_set nu & ij.2 < ij.1]].
have hne i j : i \in Lambda_set lambda -> j \in Lambda_set nu -> i != j.
  move=> hi hj; apply/eqP=> he; move: hu; rewrite Lambda_disjointE => /subsetP hd.
  have hn := hd j hj; rewrite inE -he hi in hn; by [].
have hU : S :|: T = setX (Lambda_set lambda) (Lambda_set nu).
  apply/setP=> [[i j]]; rewrite in_setU /S /T !inE.
  have hi := hne i j.
  rewrite /Lambda_set !inE in hi.
  case hl: (i \in val lambda); case hn: (j \in val nu) => //=.
  have hij := hi hl hn.
  by rewrite -neq_ltn val_eqE hij.
have hI : S :&: T = set0.
  apply/setP=> [[i j]]; rewrite /S /T !inE.
  case: (i \in val lambda); case: (j \in val nu) => //=.
  case hij: (i < j) => //=.
  have hji : ~~ (j < i) by rewrite ltnNge negbK; apply: ltnW; rewrite hij.
  by rewrite (negbTE hji).
have hc := cardsUI S T.
by rewrite hU hI cards0 addn0 cardsX !Lambda_set_card in hc; symmetry.
Qed.
End Counts.
End FedererInteriorSigns.
