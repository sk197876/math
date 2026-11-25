(** Federer (1969), 3.1.11, p. 219:
    the converse grouping of a bounded linear map into
    the abstract multilinear space. Together with currying,
    this proves the recursive identification is onto. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP TensorFamilyUP FamilyUpdate
  NormDifferentialUP ContinuousMultilinearUP MultilinearArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_uncurry_exists]:
    every continuous linear map into the k-linear space is
    a continuous (k+1)-linear map after adjoining the final
    argument. This supports the recursive derivative of
    Federer 3.1.11, p. 219, including k= 0. *)
Theorem continuous_multilinear_uncurry_exists (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (evaluation : {ffun 'I_k->X}->Hom Z Y) (ZN : Z->R)
    (hNX : is_real_norm NX)
    (hZ : is_continuous_multilinear_space NX NY evaluation ZN)
    (L : Hom X Z) :
  norm_bounded_linear NX ZN L ->
  exists f : {ffun 'I_(k+1)->X}->Y,
    norm_bounded_multilinear NX NY f /\
    forall u x, f (multilinear_arguments_join u [ffun i : 'I_1=>x])=evaluation u (L x).
Proof.
move=> [C [hC hb]].
pose f (w : {ffun 'I_(k+1)->X}) :=
  evaluation (multilinear_arguments_left w) (L (w (rshift k ord0))).
have he (u : {ffun 'I_k->X}) (v : {ffun 'I_1->X}) :
    f (multilinear_arguments_join u v)=evaluation u (L (v ord0)).
  by rewrite /f multilinear_arguments_left_join multilinear_arguments_join_right.
exists f; split; last by move=> u x; rewrite he ffunE.
split.
- move=> w i c x y.
  rewrite -[w](multilinear_arguments_join_split w).
  case: (split_ordP i)=> j ->.
  + rewrite -!multilinear_arguments_join_with_left !he.
    exact: (@continuous_multilinear_evaluation R k X Y Z NX NY evaluation ZN hZ _ _ j c x y).
  + rewrite (ord1 j) -!multilinear_arguments_join_with_right !he !family_with_in.
    by rewrite !linearP.
- exists C; split=> // w.
  rewrite -[w](multilinear_arguments_join_split w) he multilinear_arguments_product big_ord1.
  pose u := multilinear_arguments_left w.
  pose x := multilinear_arguments_right w ord0.
  have h := multilinear_operator_bound (continuous_multilinear_norm_laws hZ (L x)) u.
  have hp : 0<=\prod_(i<k) NX (u i).
    apply: prodr_ge0=> i _; exact: (real_seminorm_nonnegative hNX.1 (u i)).
  apply: le_trans h _.
  have hh := ler_wpM2r hp (hb x).
  have heq : (C*NX x)*(\prod_(i<k) NX (u i))=
    C*((\prod_(i<k) NX (u i))*NX x) by ring.
  by rewrite heq in hh.
Qed.
