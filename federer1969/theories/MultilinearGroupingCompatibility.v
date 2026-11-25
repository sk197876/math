(** Federer (1969), 3.1.11, p. 219:
    compatibility of grouped evaluation with the
    successor differential and the empty final block.
    These identities supply the induction in D^q D^p. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ContinuousMultilinearUP
  MultilinearArguments MultilinearSuccessorArguments
  MultilinearArgumentSequence MultilinearDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [multilinear_grouping_successor_iff]:
    the last argument in D(D^(p+q) f)
    may be grouped with the final q arguments,
    supporting the induction stated by Federer
    in 3.1.11, p. 219. *)
Theorem multilinear_grouping_successor_iff (R : realType) p q
    (X Y P W W' : lmodType R) (Z : nat->lmodType R)
    (NX : X->R) (NY : Y->R)
    (ep : {ffun 'I_p->X}->Hom P Y) (PN : P->R)
    (hP : is_continuous_multilinear_space NX NY ep PN)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ew : {ffun 'I_q->X}->Hom W P)
    (ew' : {ffun 'I_q.+1->X}->Hom W' P)
    (J : Hom (Z (p+q)) W) (J' : Hom (Z (p+q.+1)) W') :
  (forall z u v, ep u (ew v (J z))=@ez (p+q) (multilinear_arguments_join u v) z) ->
  (forall z u v, ep u (ew' v (J' z))=@ez (p+q.+1) (multilinear_arguments_join u v) z) ->
  forall (L : Hom X (Z (p+q))) (z : Z (p+q.+1)),
    (forall u x, @ez (p+q) u (L x)=
      @ez (p+q).+1 (multilinear_successor_arguments u x)
        (multilinear_degree_cast Z (addnS p q) z)) <->
    (forall v x, ew v (hom_comp J L x)=
      ew' (multilinear_successor_arguments v x) (J' z)).
Proof.
move=> hJ hJ' L z; split.
- move=> hL v x; apply: (continuous_multilinear_extensional hP)=>u.
  rewrite hom_compE hJ hL -multilinear_arguments_join_successor
    multilinear_degree_cast_evaluation hJ'.
  by [].
- move=> hL u x.
  have hh := congr1 (ep (multilinear_arguments_left u))
    (hL (multilinear_arguments_right u) x).
  rewrite hom_compE hJ hJ' multilinear_arguments_join_split in hh.
  have ht := multilinear_arguments_join_successor
    (multilinear_arguments_left u) (multilinear_arguments_right u) x.
  rewrite multilinear_arguments_join_split in ht.
  by rewrite -ht multilinear_degree_cast_evaluation.
Qed.

(** Source for [multilinear_grouping_zero]:
    the q= 0 grouping is the identity on
    the p-linear value space, supporting the
    base case of Federer 3.1.11, p. 219. *)
Theorem multilinear_grouping_zero (R : realType) p
    (X Y W : lmodType R) (Z : nat->lmodType R)
    (NX : X->R) (NY : Y->R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hP : is_continuous_multilinear_space NX NY (@ez p) (@ZN p))
    (ew : {ffun 'I_0->X}->Hom W (Z p))
    (J : Hom (Z (p+0)) W) :
  (forall z u v, @ez p u (ew v (J z))=
    @ez (p+0) (multilinear_arguments_join u v) z) ->
  forall z v, ew v (J z)=multilinear_degree_cast Z (addn0 p) z.
Proof.
move=> hJ z v; apply: (continuous_multilinear_extensional hP)=>u.
rewrite hJ.
have hh := @multilinear_degree_cast_evaluation R X Y Z ez
  (p+0)%N p (addn0 p) z (multilinear_arguments_join u v).
rewrite multilinear_arguments_join_empty_right in hh.
exact: esym hh.
Qed.
