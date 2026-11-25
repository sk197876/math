(** Federer (1969), 3.1.11, p. 220:
    combining symmetry of the preceding arguments
    with exchange of the final pair. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import MultilinearArguments MultilinearSuccessorArguments
  FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** Source for [multilinear_successor_lift]:
    evaluation at a preceding argument after adjoining
    the last argument, supporting Federer 3.1.11,
    pp. 219–220. *)
Lemma multilinear_successor_lift (T : Type) n
    (u : {ffun 'I_n->T}) (x : T) (i : 'I_n) :
  multilinear_successor_arguments u x (lift ord_max i)=u i.
Proof.
rewrite /multilinear_successor_arguments /multilinear_arguments_cast ffunE.
have hi : cast_ord (esym (addn1 n)) (lift ord_max i)=lshift 1 i.
  apply: val_inj.
  change ((lift ord_max i : nat)=(i : nat)).
  exact: lift_max.
by rewrite hi multilinear_arguments_join_left.
Qed.

(** Source for [multilinear_successor_last]:
    evaluation at the adjoined last argument,
    supporting Federer 3.1.11, pp. 219–220. *)
Lemma multilinear_successor_last (T : Type) n
    (u : {ffun 'I_n->T}) (x : T) :
  multilinear_successor_arguments u x ord_max=x.
Proof.
rewrite /multilinear_successor_arguments /multilinear_arguments_cast ffunE.
have hi : cast_ord (esym (addn1 n)) ord_max=rshift n ord0.
  apply: val_inj; by rewrite /= addn0.
by rewrite hi multilinear_arguments_join_right ffunE.
Qed.

(** Source for [multilinear_successor_permutation]:
    a permutation of preceding arguments extends by
    fixing the last argument, supporting the symmetry
    induction in Federer 3.1.11, p. 220. *)
Lemma multilinear_successor_permutation (T : Type) n
    (u : {ffun 'I_n->T}) (x : T) (s : 'S_n) :
  finite_argument_permutation (lift_perm ord_max ord_max s)
    (multilinear_successor_arguments u x)=
  multilinear_successor_arguments (finite_argument_permutation s u) x.
Proof.
apply/ffunP=>i; rewrite /finite_argument_permutation ffunE.
case: (unliftP ord_max i)=>[j|] ->.
- by rewrite lift_perm_lift !multilinear_successor_lift ffunE.
- by rewrite lift_perm_id !multilinear_successor_last.
Qed.

(** Source for [multilinear_successor_last_pair]:
    exchanging the last two positions exchanges their
    two argument values, supporting the D^2 D^(k-2)
    step in Federer 3.1.11, p. 220. *)
Lemma multilinear_successor_last_pair (T : Type) n
    (u : {ffun 'I_n->T}) (x y : T) :
  finite_argument_permutation
    (tperm (lift (ord_max : 'I_n.+2) ord_max) ord_max)
    (multilinear_successor_arguments (multilinear_successor_arguments u x) y)=
  multilinear_successor_arguments (multilinear_successor_arguments u y) x.
Proof.
apply/ffunP=>i; rewrite /finite_argument_permutation ffunE.
case: (unliftP (ord_max : 'I_n.+2) i)=>[j|] ->.
- case: (unliftP (ord_max : 'I_n.+1) j)=>[k|] ->.
  + have hne : lift (ord_max : 'I_n.+2) ord_max!=
        lift ord_max (lift (ord_max : 'I_n.+1) k).
      by rewrite (inj_eq (@lift_inj n.+2 ord_max)) neq_lift.
    by rewrite (tpermD hne (neq_lift _ _)) !multilinear_successor_lift.
  + by rewrite tpermL multilinear_successor_last
      multilinear_successor_lift multilinear_successor_last.
- by rewrite tpermR multilinear_successor_lift !multilinear_successor_last.
Qed.

(** Source for [multilinear_prefix_last_pair_symmetric]:
    prefix symmetry together with symmetry of the
    last pair implies full symmetry, completing
    the finite argument step in Federer 3.1.11,
    p. 220. *)
Theorem multilinear_prefix_last_pair_symmetric (T U : Type) n
    (F : {ffun 'I_n.+2->T}->U) :
  (forall (s : 'S_n.+1) u x,
    F (multilinear_successor_arguments (finite_argument_permutation s u) x)=
      F (multilinear_successor_arguments u x)) ->
  (forall u x y,
    F (multilinear_successor_arguments (multilinear_successor_arguments u x) y)=
      F (multilinear_successor_arguments (multilinear_successor_arguments u y) x)) ->
  forall s u, F (finite_argument_permutation s u)=F u.
Proof.
move=> hprefix hlast.
apply: (finite_star_transposition_symmetry
  (a:=lift (ord_max : 'I_n.+2) (ord_max : 'I_n.+1)))=>j w.
have [v [y ->]] := multilinear_successor_arguments_surjective w.
case: (unliftP (ord_max : 'I_n.+2) j)=>[i|] ->.
- by rewrite -lift_permutation_transposition multilinear_successor_permutation hprefix.
- have [u [x ->]] := multilinear_successor_arguments_surjective v.
  rewrite multilinear_successor_last_pair; exact: esym (hlast u x y).
Qed.
