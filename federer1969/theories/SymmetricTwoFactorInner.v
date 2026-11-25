(** Federer (1969), 3.2.28(4), printed p. 266:
    DT preserves tangent lengths on the unit sphere.
    This supporting degree-two inner-product formula expands
    the two actual permutations in 1.10.5, p. 47. *)
From mathcomp Require Import all_boot all_order all_algebra reals fingroup perm.
From Federer Require Import InnerProductUP SymmetricGrading SymmetricFormIsomorphism
  InnerSymmetric InnerSymmetricPermutationFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [two_permutation_sum]: the two terms of the
    symmetric degree-two pairing in 1.10.5, p. 47,
    supporting the tangent isometry of Federer 3.2.28(4),
    p. 266. This is finite-index bookkeeping. *)
Lemma two_permutation_sum (A:zmodType) (F:'S_2->A):
  \sum_(s:'S_2) F s=F 1%g+F (tperm ord0 ord_max).
Proof.
pose t:'S_2:=tperm ord0 ord_max.
have hDist:(1%g:'S_2)!=t.
  apply/eqP=>he.
  have h:=congr1 (fun s:'S_2=>s ord0) he.
  rewrite perm1 /t tpermL in h.
  have hn:=congr1 val h; discriminate hn.
have hSet:[set:'S_2]=[set 1%g;t].
  apply/eqP; rewrite eq_sym eqEcard subsetT cards2 hDist cardsT card_Sn /=.
  reflexivity.
have he:(\sum_(s:'S_2) F s)=\sum_(s in [set:'S_2]) F s.
  by apply:eq_bigl=>s; rewrite in_setT.
by rewrite he hSet big_setU1 ?in_set1 ?hDist // big_set1.
Qed.

(** Source for [symmetric_two_factor_inner]: the exact pairing
    (ab).(cd)=(a.c)(b.d)+(a.d)(b.c), from
    1.10.5, p. 47. Supporting |DT(x)h|=|h|
    for unit x perpendicular to h in Federer 3.2.28(4), p. 266. *)
Lemma symmetric_two_factor_inner (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) a b c d:
  symmetric_inner_form hB (symmetric_tuple_component [tuple a;b])
    (symmetric_tuple_component [tuple c;d])=
    B a c*B b d+B b c*B a d.
Proof.
rewrite symmetric_inner_tuple_permutations two_permutation_sum.
rewrite !big_ord_recr !big_ord0 ?mul1r ?perm1.
have hw:widen_ord (leqnSn 1) (ord_max:'I_1)=(ord0:'I_2) by apply:val_inj.
rewrite hw.
change ((1*B a c)*(B b d)+
  (1*B (tnth [tuple a;b] (tperm ord0 ord_max ord0)) c)*
    B (tnth [tuple a;b] (tperm ord0 ord_max ord_max)) d=
  B a c*B b d+B b c*B a d).
by rewrite tpermL tpermR !(tnth_nth 0) /= !mul1r.
Qed.
