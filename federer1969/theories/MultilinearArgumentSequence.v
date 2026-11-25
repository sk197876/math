(** Federer (1969), 3.1.11, p. 219:
    finite-argument bookkeeping for regrouping successive
    higher differentials. Equality transports only
    natural-number arities, never mathematical values. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ConcatenatedFamilies MultilinearArguments MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [multilinear_argument_sequence]:
    the ordered argument list of a higher
    differential, used to compare the two groupings
    in Federer 3.1.11, p. 219. *)
Definition multilinear_argument_sequence (T : Type) n (u : {ffun 'I_n->T}) :=
  [seq u i | i<-enum 'I_n].

(** Source for [multilinear_argument_sequence_injective]:
    equality of ordered lists determines the
    argument family, supporting the grouping identity
    in Federer 3.1.11, p. 219. *)
Lemma multilinear_argument_sequence_injective (T : Type) n :
  injective (@multilinear_argument_sequence T n).
Proof.
move=> u v he; apply/ffunP=>i.
have hh := congr1 (fun s=>nth (u i) s i) he.
rewrite /multilinear_argument_sequence
  !(nth_map i) ?size_enum_ord ?ltn_ord // in hh.
have hi : nth i (Finite.enum [the finType of 'I_n]) i = i.
  by rewrite -enumT nth_ord_enum.
by rewrite !hi in hh.
all: by rewrite -enumT size_enum_ord ltn_ord.
Qed.

(** Source for [multilinear_argument_sequence_cast]:
    changing only an equal arity preserves the
    ordered list, supporting Federer 3.1.11, p. 219. *)
Lemma multilinear_argument_sequence_cast (T : Type) m n (h : m=n)
    (u : {ffun 'I_m->T}) :
  multilinear_argument_sequence (multilinear_arguments_cast h u)=
    multilinear_argument_sequence u.
Proof. subst n; by rewrite multilinear_arguments_cast_reflexive. Qed.

(** Source for [multilinear_argument_sequence_join]:
    grouping consecutive arguments concatenates their
    ordered lists, supporting Federer 3.1.11, p. 219. *)
Lemma multilinear_argument_sequence_join (T : Type) m n
    (u : {ffun 'I_m->T}) (v : {ffun 'I_n->T}) :
  multilinear_argument_sequence (multilinear_arguments_join u v)=
    multilinear_argument_sequence u++multilinear_argument_sequence v.
Proof.
rewrite /multilinear_argument_sequence /multilinear_arguments_join.
transitivity [seq concatenate_family u v i | i<-enum 'I_(m+n)].
- apply: eq_map=>i; by rewrite ffunE.
- exact: concatenate_family_sequence.
Qed.

(** Source for [multilinear_argument_sequence_successor]:
    adjoining the last derivative argument appends
    one entry, supporting Federer 3.1.11, p. 219. *)
Lemma multilinear_argument_sequence_successor (T : Type) n
    (u : {ffun 'I_n->T}) (x : T) :
  multilinear_argument_sequence (multilinear_successor_arguments u x)=
    multilinear_argument_sequence u++[::x].
Proof.
rewrite /multilinear_successor_arguments multilinear_argument_sequence_cast
  multilinear_argument_sequence_join.
by rewrite /multilinear_argument_sequence enum_ordSl enum_ord0 /= ffunE.
Qed.

(** Source for [multilinear_arguments_join_successor]:
    adjoining the last argument commutes with
    grouping the preceding p and q arguments,
    the compatibility needed for induction on q
    in Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_join_successor (T : Type) p q
    (u : {ffun 'I_p->T}) (v : {ffun 'I_q->T}) (x : T) :
  multilinear_arguments_cast (addnS p q)
    (multilinear_arguments_join u (multilinear_successor_arguments v x))=
  multilinear_successor_arguments (multilinear_arguments_join u v) x.
Proof.
apply: multilinear_argument_sequence_injective.
rewrite multilinear_argument_sequence_cast !multilinear_argument_sequence_join
  !multilinear_argument_sequence_successor multilinear_argument_sequence_join.
by rewrite catA.
Qed.

(** Source for [multilinear_arguments_join_empty_right]:
    the p+0 grouping is the original p-tuple,
    the base case of the D^q D^p
    identity in Federer 3.1.11, p. 219. *)
Lemma multilinear_arguments_join_empty_right (T : Type) p
    (u : {ffun 'I_p->T}) (v : {ffun 'I_0->T}) :
  multilinear_arguments_cast (addn0 p) (multilinear_arguments_join u v)=u.
Proof.
apply: multilinear_argument_sequence_injective.
rewrite multilinear_argument_sequence_cast multilinear_argument_sequence_join.
by rewrite /multilinear_argument_sequence enum_ord0 /= cats0.
Qed.


(** Source for [multilinear_argument_sequence_singleton]:
    the list of a one-entry argument family,
    supporting Federer 3.1.11, pp. 219–220. *)
Lemma multilinear_argument_sequence_singleton (T : Type) (x : T) :
  multilinear_argument_sequence [ffun i : 'I_1=>x]=[::x].
Proof. by rewrite /multilinear_argument_sequence enum_ordSl enum_ord0 /= ffunE. Qed.

(** Source for [multilinear_arguments_join_pair]:
    a final two-argument block is the same
    ordered family as two successive appended
    arguments, supporting Federer 3.1.11, p. 220. *)
Lemma multilinear_arguments_join_pair (T : Type) n
    (h : (n+2)%N=n.+2) (u : {ffun 'I_n->T}) (x y : T) :
  multilinear_arguments_cast h (multilinear_arguments_join u
    (multilinear_successor_arguments [ffun i : 'I_1=>x] y))=
  multilinear_successor_arguments (multilinear_successor_arguments u x) y.
Proof.
apply: multilinear_argument_sequence_injective.
rewrite multilinear_argument_sequence_cast multilinear_argument_sequence_join
  !multilinear_argument_sequence_successor multilinear_argument_sequence_singleton.
by rewrite catA.
Qed.
