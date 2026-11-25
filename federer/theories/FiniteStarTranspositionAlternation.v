(** Federer (1969), 4.1.11, p. 366: a sign change
    under the required vertex exchanges extends to every
    permutation. Reuse the finite-permutation action,
    conjugation and transposition decomposition already used
    for 3.1.11, p. 220, and the Chapter 1 index laws. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_star_transposition_alternation]:
    exchanges with one fixed vertex suffice for the
    original orientation sign, supporting Federer
    4.1.11, p. 366. Only genuine exchanges are required;
    exchanging a position with itself remains the identity. *)
Theorem finite_star_transposition_alternation (K:fieldType) (I:finType) (T:Type)
    (W:lmodType K) (F:{ffun I->T}->W) (a:I):
  (forall j,j!=a->forall u,F (finite_argument_permutation (tperm a j) u)= -F u)->
  forall i j,i!=j->forall u,F (finite_argument_permutation (tperm i j) u)= -F u.
Proof.
move=>hStar i j hij u.
case:(eqVneq i a)=>[hEqual|hia].
  subst i.
  have hja:j!=a by rewrite eq_sym.
  exact:(hStar j hja u).
case:(eqVneq j a)=>[hEqual|hja].
  subst j;rewrite tpermC;exact:(hStar i hia u).
have haj:a!=j by rewrite eq_sym.
rewrite -(tpermJ_tperm haj hij) conjgE tpermV !finite_argument_permutation_mul.
by rewrite (hStar i hia) (hStar j hja) (hStar i hia) opprK.
Qed.

(** Source for [finite_transposition_parity_alternation]:
    each original finite permutation acts by its parity
    sign once every genuine exchange acts by minus one,
    supporting the permutation clause in Federer 4.1.11,
    p. 366. The ordinary finite transposition decomposition
    is reused, including empty and singleton index types. *)
Theorem finite_transposition_parity_alternation (K:fieldType) (I:finType) (T:Type)
    (W:lmodType K) (F:{ffun I->T}->W):
  (forall i j,i!=j->forall u,F (finite_argument_permutation (tperm i j) u)= -F u)->
  forall s u,F (finite_argument_permutation s u)=(-1:K)^+(odd_perm s)*:F u.
Proof.
move=>hSwap s.
have[ts -> hDistinct]:=prod_tpermP s.
elim:ts hDistinct=>[|[i j] ts ih] /= hDistinct u.
- by rewrite big_nil finite_argument_permutation_one odd_perm1 expr0 scale1r.
- move/andP:hDistinct=>[hij hRest].
  rewrite big_cons finite_argument_permutation_mul (hSwap i j hij) (ih hRest)
    odd_mul_tperm hij /=.
  by case:(odd_perm _)=>/=;rewrite ?expr0 ?expr1 ?scale1r ?scaleN1r ?opprK.
Qed.
