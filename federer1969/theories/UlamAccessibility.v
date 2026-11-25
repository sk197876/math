(** Federer (1969), 2.1.6, p. 59, final paragraph: accessibility and the
    least possible non-Ulam cardinal. Cardinalities are represented by sets.
    A cofinal family of initial ordinal representatives has union the limit
    cardinal; the certificate below records that union up to equipollence.
    The final printed consistency remark is metamathematical, not an
    additional axiom of this formalisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import UlamCardinalUP UlamCountable UlamUnion
  CardinalSuccessorUP UlamSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [is_accessible_cardinal]: Federer 2.1.6,
    p. 59, definition of accessible cardinal, paraphrased: it is
    a successor or is the supremum of a family of smaller cardinals
    indexed by a smaller cardinal. The union certificate gives the
    printed supremum when using initial ordinal representatives.
    Representatives of smaller cardinals can be subsets of D. *)
Definition is_accessible_cardinal (I : choiceType) (D : set I) :=
  (exists A : set I, is_cardinal_successor A D) \/
  exists (J : choiceType) (S : set J) (F : J -> set I),
    S #<= D /\ ~ (D #<= S) /\
    (forall j, S j -> F j #<= D /\ ~ (D #<= F j)) /\
    D #= (\bigcup_(j in S) F j).

(** Source for [is_least_non_ulam_set]: Federer 2.1.6,
    p. 59, conditional hypothesis that there is a least cardinal
    which is not Ulam. The predicate asserts no existence: D is
    not Ulam, and every strictly smaller cardinal is Ulam. *)
Definition is_least_non_ulam_set (R : realType) (I : choiceType) (D : set I) :=
  ~ is_ulam_set R D /\
  forall (J : choiceType) (A : set J), A #<= D -> ~ (D #<= A) -> is_ulam_set R A.

(** Source for [least_non_ulam_not_accessible]: Federer
    2.1.6, p. 59, conclusion from (1) and (2): the least
    non-Ulam cardinal, if there is one, cannot be accessible.
    The successor and smaller-cofinal-family alternatives each
    contradict its minimality. No existence or consistency claim
    is assumed or asserted. *)
Theorem least_non_ulam_not_accessible (R : realType) (I : choiceType) (D : set I) :
  is_least_non_ulam_set R D -> ~ is_accessible_cardinal D.
Proof.
move=> [hn hsmall] [[A hs]|[J [S [F [hSD [hDS [hF he]]]]]]]; apply: hn.
- have huA := hsmall I A hs.1 hs.2.1.
  exact: (@ulam_set_successor R I I A D huA hs).
- have huS := hsmall J S hSD hDS.
  have huF j : S j -> is_ulam_set R (F j).
    move=> hj; exact: hsmall I (F j) (hF j hj).1 (hF j hj).2.
  have hu := ulam_set_union huS huF.
  exact: (proj2 (@ulam_set_cardinal_invariant R _ _ D _ he) hu).
Qed.

(** Source for [least_non_ulam_uncountable]: Federer 2.1.6,
    pp. 58-59, supporting consequence: a non-Ulam cardinal cannot
    be countable, since aleph zero and all smaller cardinals are Ulam. *)
Lemma least_non_ulam_uncountable (R : realType) (I : choiceType) (D : set I) :
  is_least_non_ulam_set R D -> ~ countable D.
Proof. move=> [hn _] hc; apply: hn; exact: ulam_set_countable hc. Qed.
