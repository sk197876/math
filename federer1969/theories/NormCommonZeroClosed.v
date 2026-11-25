(** Federer (1969), 3.4.8(10), p. 332:
    the actual common zero system is
    closed on a closed subset of
    its original domain. The open-union
    argument of 3.4.2(7), p. 312,
    applies to arbitrary continuous normed maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormClassZeroNonzeroLocus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CommonZero.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variables A S:set X.
Variable index:Type.
Variable f:index->X->Y.
Hypothesis hF:forall i,norm_class_zero NX NY A (f i).
Hypothesis hSA:S `<=` A.

(** Source for [norm_common_zero_closed_form]:
    the complement of the common zero
    set is an open union of
    nonzero loci, supporting 3.4.8(10), p. 332,
    as in 3.4.2(7), p. 312.
    The index family may be infinite. *)
Theorem norm_common_zero_closed_form:
  exists O:set X,@open (real_norm_metric_space hNX) O /\
    (S `&` [set x|forall i,f i x = 0]) = S `&` ~` O.
Proof.
pose O:set X:=\bigcup_(i in @setT index) [set x|A x /\f i x!=0].
have hOpen:@open (real_norm_metric_space hNX) O.
  apply:bigcup_open=>i _.
  exact:(@norm_class_zero_nonzero_locus_open R X Y NX NY hNX hNY A (f i) (hF i)).
exists O;split;first exact:hOpen.
apply/seteqP;split.
- move=>x [hs hZero];split;first exact:hs.
  move=>[i _ [ha hNonzero]];by rewrite hZero eqxx in hNonzero.
- move=>x [hs hNot];split;first exact:hs.
  move=>i;case:(eqVneq (f i x) 0)=>[hZero|hNonzero];first exact:hZero.
  exfalso;apply:hNot;exists i;first exact:Logic.I.
  by split;[exact:hSA x hs|exact:hNonzero].
Qed.

(** Source for [norm_common_zero_on_closed_subset]:
    the common original equations cut a
    closed set out of any closed
    subset inside their actual domain,
    3.4.8(10), p. 332. No global
    continuation or global continuity is required. *)
Theorem norm_common_zero_on_closed_subset:
  @closed (real_norm_metric_space hNX) S ->
  @closed (real_norm_metric_space hNX) (S `&` [set x|forall i,f i x = 0]).
Proof.
move=>hClosed.
have [O [hOpen ->]]:=norm_common_zero_closed_form.
exact:closedI hClosed (open_closedC hOpen).
Qed.
End CommonZero.
