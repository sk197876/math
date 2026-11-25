(** Federer (1969), 3.1.11, p. 220:
    summing an ordered multilinear expression over
    all argument permutations produces a symmetric
    continuous multilinear form. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm reals.
From Federer Require Import FamilyUpdate TensorFamilyUP RealNormUP
  ContinuousMultilinearUP FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_argument_permutation_update]:
    an update at position i moves
    to position s^(-1)(i), supporting the
    permutation sum in Federer 3.1.11,
    p. 220. *)
Lemma finite_argument_permutation_update k (T : Type)
    (s : 'S_k) (u : {ffun 'I_k->T}) i x :
  finite_argument_permutation s (@family_with k (fun _=>T) u i x)=
    @family_with k (fun _=>T) (finite_argument_permutation s u) (s^-1%g i) x.
Proof.
apply/ffunP=>j; rewrite /finite_argument_permutation ffunE.
case:(eqVneq i (s j))=>[hi|hi].
- have hj : s^-1%g i=j by rewrite hi permK.
  by rewrite hi permK !family_with_in.
- have hj : s^-1%g i!=j.
    by apply/negP=>/eqP he; move:hi; rewrite -he permKV eqxx.
  by rewrite !family_with_out // ffunE.
Qed.

(** Source for [multilinear_permuted_arguments]:
    every summand in the printed inverse
    differential is multilinear, Federer 3.1.11,
    p. 220. *)
Lemma multilinear_permuted_arguments (K : fieldType) k
    (X Y : lmodType K) (f : {ffun 'I_k->X}->Y) (s : 'S_k) :
  multilinear f -> multilinear (fun u : {ffun 'I_k->X}=>f (finite_argument_permutation s u)).
Proof.
move=>hf u i c x y; rewrite !finite_argument_permutation_update.
exact: hf.
Qed.

(** Source for [multilinear_permutation_sum]:
    the unsigned symmetrization used in the
    inverse differential on Federer 3.1.11,
    p. 220; the sign is part
    of the ordered summand. *)
Definition multilinear_permutation_sum (Y : zmodType) k (X : Type)
    (f : {ffun 'I_k->X}->Y) u :=
  \sum_(s : 'S_k) f (finite_argument_permutation s u).

(** Source for [multilinear_permutation_sum_multilinear]:
    the permutation sum is multilinear,
    Federer 3.1.11, p. 220. *)
Lemma multilinear_permutation_sum_multilinear (K : fieldType) k
    (X Y : lmodType K) (f : {ffun 'I_k->X}->Y) :
  multilinear f -> multilinear (multilinear_permutation_sum f).
Proof.
move=>hf u i c x y; rewrite /multilinear_permutation_sum scaler_sumr -big_split.
apply: eq_bigr=>s _; exact (@multilinear_permuted_arguments K k X Y f s hf u i c x y).
Qed.

(** Source for [multilinear_permutation_sum_symmetric]:
    reindexing the finite permutation group
    proves symmetry of the inverse differential
    expression, Federer 3.1.11, p. 220. *)
Lemma multilinear_permutation_sum_symmetric (Y : zmodType) k (X : Type)
    (f : {ffun 'I_k->X}->Y) (t : 'S_k) u :
  multilinear_permutation_sum f (finite_argument_permutation t u)=
    multilinear_permutation_sum f u.
Proof.
rewrite /multilinear_permutation_sum.
under eq_bigr do rewrite -finite_argument_permutation_mul.
by rewrite [RHS](reindex (fun s : 'S_k=>(s*t)%g)
  (onW_bij _ (injF_bij (mulIg t)))).
Qed.

(** Source for [multilinear_permutation_sum_diagonal]:
    repeated arguments make all k! summands
    equal, including the single empty permutation
    when k= 0, Federer 3.1.11,
    p. 220. *)
Lemma multilinear_permutation_sum_diagonal (K : fieldType) k
    (X : Type) (Y : lmodType K) (f : {ffun 'I_k->X}->Y) x :
  multilinear_permutation_sum f [ffun _ : 'I_k=>x]=
    (k`!)%:R*:f [ffun _ : 'I_k=>x].
Proof.
rewrite /multilinear_permutation_sum.
have he s : finite_argument_permutation s [ffun _ : 'I_k=>x]=[ffun _ : 'I_k=>x].
  by apply/ffunP=>i; rewrite /finite_argument_permutation !ffunE.
under eq_bigr do rewrite he.
by rewrite sumr_const card_Sn -scaler_nat.
Qed.

(** Source for [multilinear_permutation_sum_bound]:
    the norm of the symmetrized form is
    at most k! times the ordered
    product bound, supporting the inverse formula
    in Federer 3.1.11, p. 220. *)
Lemma multilinear_permutation_sum_bound (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNY : is_real_norm NY) (f : {ffun 'I_k->X}->Y) C :
  (forall u, NY (f u)<=C*\prod_(i<k) NX (u i)) ->
  forall u, NY (multilinear_permutation_sum f u)
    <=((k`!)%:R*C)*\prod_(i<k) NX (u i).
Proof.
move=>hf u; apply: le_trans (real_seminorm_sum hNY.1 _) _.
have hs s : NY (f (finite_argument_permutation s u))
    <=C*\prod_(i<k) NX (u i).
  have hh := hf (finite_argument_permutation s u).
  have he : (\prod_(i<k) NX (finite_argument_permutation s u i))=
      \prod_(i<k) NX (u i).
    under eq_bigr do rewrite /finite_argument_permutation ffunE.
    by rewrite [RHS](reindex s (onW_bij _ (injF_bij (perm_inj (s:=s))))).
  by rewrite he in hh.
have hh : (\sum_(s : 'S_k) NY (f (finite_argument_permutation s u))) <=
    \sum_(s : 'S_k) C*\prod_(i<k) NX (u i).
  apply: ler_sum=>s _; exact: hs.
by rewrite sumr_const card_Sn -mulr_natl mulrA in hh.
Qed.
