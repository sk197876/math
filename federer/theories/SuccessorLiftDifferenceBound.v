(** Federer (1969), 3.1.15, p. 228: the difference of two
    successor lifts. When z and z' in the continuous
    (K+1)-linear space are the lifts, through adjoining the last
    argument, of two bounded linear maps L and L' from X into
    the continuous K-linear space, and L'-L has operator bound
    eps, then the norm of z'-z in the sense of 3.1.11, p. 219
    (erratum p. 4, book p. 219 line 4) is at most eps. This is
    the estimate behind the statement that
    D^(k+1) P_a(b)-D^(k+1) P_b(b) = D^(k+1) f(b)-D^(k+1) f(a)
    is small for small |b-a|. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  MultilinearArguments MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LiftBound.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).

(** Source for [successor_lift_difference_bound]: Federer 3.1.15,
    p. 228, the smallness of
    D^(k+1) P_a(b)-D^(k+1) P_b(b) = D^(k+1) f(b)-D^(k+1) f(a),
    measured by the norm of 3.1.11, p. 219, erratum p. 4, book
    p. 219 line 4: the norm of a (K+1)-linear map is the least
    bound C with NY (ev w t)<=C times the product of NX (w j). *)
Theorem successor_lift_difference_bound (K : nat) (L L' : Hom X (Z K)) (z z' : Z K.+1)
    (hl : forall u v, @ev K u (L v)=@ev K.+1 (multilinear_successor_arguments u v) z)
    (hl' : forall u v, @ev K u (L' v)=@ev K.+1 (multilinear_successor_arguments u v) z')
    (eps : R) (heps : 0<=eps) (hb : forall v, @ZN K ((L'-L) v)<=eps*NX v) :
  @ZN K.+1 (z'-z)<=eps.
Proof.
have homB : forall (F G : Hom X (Z K)) h, (F-G) h=F h-G h.
  move=> F G h; rewrite -[-G]scaleN1r hom_addE hom_scaleE; by rewrite scaleN1r.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws (hZ K.+1) (z'-z)) heps).
move=> w.
have [u [v ->]] := multilinear_successor_arguments_surjective w.
have hprod : \prod_(i<K.+1) NX (multilinear_successor_arguments u v i)=
    (\prod_(i<K) NX (u i))*NX v.
  by rewrite /multilinear_successor_arguments multilinear_arguments_cast_product
    multilinear_arguments_product big_ord1 ffunE.
have hev : @ev K.+1 (multilinear_successor_arguments u v) (z'-z)=@ev K u ((L'-L) v).
  have h1 : @ev K u (L' v-L v)=@ev K u (L' v)-@ev K u (L v) by rewrite raddfB.
  have h2 : @ev K.+1 (multilinear_successor_arguments u v) (z'-z)=
      @ev K.+1 (multilinear_successor_arguments u v) z'-
      @ev K.+1 (multilinear_successor_arguments u v) z by rewrite raddfB.
  by rewrite homB h1 h2 hl hl'.
have hP : 0<=\prod_(i<K) NX (u i).
  apply: prodr_ge0=> i _; exact: (real_seminorm_nonnegative hNX.1).
rewrite hev hprod mulrA mulrAC.
apply: (le_trans (multilinear_operator_bound
  (continuous_multilinear_norm_laws (hZ K) ((L'-L) v)) u)).
exact: (ler_wpM2r hP (hb v)).
Qed.
End LiftBound.
