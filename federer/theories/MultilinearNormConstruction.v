(** Private existence proof for the continuous multilinear
    supremum norm, Federer (1969), 3.1.11, p. 219.
    Scalar completeness supplies the bound without compactness
    or attainment of the unit-product supremum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP TensorFamilyUP NormMultilinearBound ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [multilinear_unit_product_bound]: supporting
    normalization for the corrected supremum in Federer
    3.1.11, p. 219, erratum p. 4, book line 4.
    The empty product is one. *)
Lemma multilinear_unit_product_bound (R : realType) k (X : lmodType R)
    (NX : X->R) (hNX : is_real_norm NX) (u : {ffun 'I_k->X}) :
  (forall i, NX (u i)<= 1) -> \prod_(i<k) NX (u i)<= 1.
Proof.
move=> hu.
have he : (\prod_(i<k) (1:R))= 1 by rewrite prodr_const expr1n.
rewrite -[X in _<=X]he.
apply: ler_prod=> i _; apply/andP; split.
- exact: (real_seminorm_nonnegative hNX.1 (u i)).
- exact: hu.
Qed.

(** Source for [multilinear_operator_norm_exists]: the
    finite norm of each continuous multilinear map in Federer
    3.1.11, p. 219, with the target norm correction
    from erratum p. 4. Degree zero is included: its
    unique input tuple may have a nonzero function value. *)
Theorem multilinear_operator_norm_exists (R : realType) k (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (f : {ffun 'I_k->X}->Y) :
  norm_bounded_multilinear NX NY f -> exists c, is_multilinear_operator_norm NX NY f c.
Proof.
move=> [hf [C [hC hb]]].
pose S := [set r : R | exists u : {ffun 'I_k->X},
  (forall i, NX (u i)<= 1) /\ r=NY (f u)].
pose z : {ffun 'I_k->X} := [ffun i=> 0].
have hz : forall i, NX (z i)<= 1.
  by move=> i; rewrite /z ffunE (real_seminorm_zero hNX.1).
have hs0 : S (NY (f z)) by exists z.
have hs : S!=set0 by exists (NY (f z)).
have hCbound : ubound S C.
  move=> r [u [hu ->]]; apply: le_trans (hb u) _.
  have hh := ler_wpM2l hC (multilinear_unit_product_bound hNX hu).
  by rewrite mulr1 in hh.
have hbounded : has_ubound S by exists C.
have hn : 0<=sup S.
  exact: le_trans (real_seminorm_nonnegative hNY.1 _) (ub_le_sup hbounded hs0).
exists (sup S); constructor=> //.
- apply: (@norm_multilinear_normalized_bound R k (fun _=>X) Y
    (fun _=>NX) NY (fun _=>hNX) hNY f hf (sup S)).
  move=> u hu.
  have hm : S (NY (f u)) by exists u.
  exact: (ub_le_sup hbounded hm).
- move=> D hD hd; apply: ge_sup hs _=> r [u [hu ->]].
  apply: le_trans (hd u) _.
  have hh := ler_wpM2l hD (multilinear_unit_product_bound hNX hu).
  by rewrite mulr1 in hh.
Qed.
