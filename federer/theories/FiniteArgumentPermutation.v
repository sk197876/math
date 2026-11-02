(** Federer (1969), 3.1.11, p. 220:
    finite permutation bookkeeping for symmetry of
    higher differentials. The underlying finite-permutation
    algebra is the same background used in Chapter 1. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** Source for [finite_argument_permutation]:
    rearrangement of the argument positions in a
    symmetric higher differential, Federer 3.1.11,
    p. 220; compare 1.10.1, pp. 43–44. *)
Definition finite_argument_permutation (I : finType) (T : Type)
    (s : {perm I}) (u : {ffun I->T}) : {ffun I->T} :=
  [ffun i=>u (s i)].

(** Source for [finite_argument_permutation_one]:
    the identity rearrangement, supporting symmetry
    in Federer 3.1.11, p. 220. *)
Lemma finite_argument_permutation_one (I : finType) (T : Type)
    (u : {ffun I->T}) :
  finite_argument_permutation (1 : {perm I}) u=u.
Proof. by apply/ffunP=>i; rewrite /finite_argument_permutation ffunE perm1. Qed.

(** Source for [finite_argument_permutation_mul]:
    composition of argument rearrangements, supporting
    symmetry in Federer 3.1.11, p. 220. *)
Lemma finite_argument_permutation_mul (I : finType) (T : Type)
    (s t : {perm I}) (u : {ffun I->T}) :
  finite_argument_permutation (s*t) u=
    finite_argument_permutation s (finite_argument_permutation t u).
Proof. by apply/ffunP=>i; rewrite /finite_argument_permutation !ffunE permM. Qed.

(** Source for [finite_transposition_symmetry]:
    invariance under all transpositions implies
    invariance under every argument permutation,
    supporting Federer 3.1.11, p. 220. *)
Theorem finite_transposition_symmetry (I : finType) (T U : Type)
    (F : {ffun I->T}->U) :
  (forall i j u, F (finite_argument_permutation (tperm i j) u)=F u) ->
  forall s u, F (finite_argument_permutation s u)=F u.
Proof.
move=> hswap s.
have [ts -> _] := prod_tpermP s.
elim: ts=>[|[i j] ts ih] u.
- by rewrite big_nil finite_argument_permutation_one.
- by rewrite big_cons finite_argument_permutation_mul hswap ih.
Qed.

(** Source for [finite_star_transposition_symmetry]:
    exchanges with one fixed position already
    suffice for full symmetry. This supports the
    induction from prefix symmetry and the final
    pair exchange in Federer 3.1.11, p. 220. *)
Theorem finite_star_transposition_symmetry (I : finType) (T U : Type)
    (F : {ffun I->T}->U) (a : I) :
  (forall j u, F (finite_argument_permutation (tperm a j) u)=F u) ->
  forall s u, F (finite_argument_permutation s u)=F u.
Proof.
move=> hstar; apply: finite_transposition_symmetry=>i j u.
case: (eqVneq i j)=>[->|hij].
- by rewrite tperm1 finite_argument_permutation_one.
case: (eqVneq j a)=>[->|hja].
- by rewrite tpermC hstar.
have haj : a!=j by rewrite eq_sym.
rewrite -(tpermJ_tperm haj hij) conjgE tpermV !finite_argument_permutation_mul.
by rewrite !hstar.
Qed.

(** Source for [lift_permutation_transposition]:
    extending a transposition by one fixed argument
    preserves the exchanged positions, supporting the
    prefix step in Federer 3.1.11, p. 220. *)
Lemma lift_permutation_transposition n (p : 'I_n.+1) (i j : 'I_n) :
  lift_perm p p (tperm i j)=tperm (lift p i) (lift p j).
Proof.
apply/permP=>k; case: (unliftP p k)=>[k'|] ->.
- rewrite lift_perm_lift inj_tperm //; exact: lift_inj.
- by rewrite lift_perm_id tpermD // eq_sym neq_lift.
Qed.
