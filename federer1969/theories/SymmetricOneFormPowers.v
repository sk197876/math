(** Federer (1969), 1.10.5, p. 47: algebra-valued powers of one-forms. The
    coefficient algebra need not have a unit. The right-associated product
    gives the usual power when multiplication is associative; the evaluation
    formula itself needs only bilinearity. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm reals.
From Federer Require Import TensorUP Bilinear Hom BoundedHom SymmetricAlgebra
  SymmetricGrading SymmetricForms SymmetricFormWords SymmetricFormSum SymmetricFormProduct
  NonemptyProduct SymmetricAlgebraOneForms RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [constant_map_nseq]: Federer 1.10.5, p. 47,
    supporting list identity for repeated factors: mapping a constant
    over a finite list repeats that value as many times as its length. *)
Lemma constant_map_nseq (A B : Type) (b:B) (s:seq A) :
  [seq b | i <- s] = nseq (size s) b.
Proof. by elim: s=> [|x s ih] //=; rewrite ih. Qed.

(** Source for [symmetric_one_form_power]: Federer 1.10.5,
    p. 47, the positive integral power of a one-form, obtained
    by restricting its actual graded algebra power to that degree.
    The zero-degree value is an unused zero default in a nonunital algebra. *)
Definition symmetric_one_form_power (K : fieldType) (V W : lmodType K)
    (mu : W -> W -> W) (hmu : bilinear mu) (f : S_m V W 1) m : S_m V W m :=
  sform_component m (nonempty_product (symmetric_forms_product hmu) 0
    (nseq m (sform_include f))).

(** Source for [symmetric_one_form_power_permutations]: Federer
    1.10.5, p. 47, supporting expansion of a positive power
    into m! ordered products of the one-form's values. *)
Lemma symmetric_one_form_power_permutations (K : fieldType) (V W : lmodType K)
    (mu : W -> W -> W) (hmu : bilinear mu) (f : S_m V W 1) m
    (hm : (0<m)%N) (t : m.-tuple V) :
  symmetric_one_form_power hmu f m t =
    \sum_(sigma : 'S_m) nonempty_product mu 0
      [seq sform_words f [::tnth t (sigma i)] | i <- enum 'I_m].
Proof.
rewrite /symmetric_one_form_power sform_componentE.
have hh := @algebra_one_form_product_permutations K V W mu hmu m (fun i=>f) t hm.
by rewrite constant_map_nseq size_enum_ord in hh.
Qed.

(** Source for [symmetric_one_form_power_diagonal]: Federer
    1.10.5, p. 47, supporting diagonal identity. Evaluating
    the m-th power on m equal vectors gives m! times the m-th
    coefficient-algebra power of the one-form's value. *)
Lemma symmetric_one_form_power_diagonal (K : fieldType) (V W : lmodType K)
    (mu : W -> W -> W) (hmu : bilinear mu) (f : S_m V W 1) m
    (hm : (0<m)%N) x :
  symmetric_one_form_power hmu f m [tuple x | i<m] =
    (m`!)%:R *: nonempty_product mu 0 (nseq m (f [tuple x])).
Proof.
rewrite (symmetric_one_form_power_permutations hmu f hm).
have hs : forall sigma:'S_m,
  [seq sform_words f [::tnth [tuple x | j<m] (sigma i)] | i<-enum 'I_m]
    = nseq m (f [tuple x]).
  move=> sigma.
  transitivity ([seq f [tuple x] | i<-enum 'I_m]).
  - apply: eq_map=> i; rewrite tnth_mktuple; exact: (sform_wordsE f [tuple x]).
  - by rewrite constant_map_nseq size_enum_ord.
under eq_bigr do rewrite hs.
by rewrite sumr_const card_Sn -scaler_nat.
Qed.

(** Source for [nonempty_product_seminorm_bound]: Federer
    1.10.5, p. 47, supporting submultiplicative estimate.
    A list of coefficient vectors of lengths at most L has product
    length at most L raised to its length. The empty zero default
    also satisfies this inequality. *)
Lemma nonempty_product_seminorm_bound (R : realFieldType) (W : lmodType R)
    (N : W -> R) (hN : is_real_seminorm N) (mu : W -> W -> W)
    (hsub : forall x y, N (mu x y)<=N x*N y) L (hL : 0<=L) (s:seq W) :
  (forall x, x\in s -> N x<=L) -> N (nonempty_product mu 0 s)<=L^+(size s).
Proof.
elim: s=> [|x s ih] hb; first by rewrite /= (real_seminorm_zero hN) expr0 ler01.
have hx : N x<=L := hb x (mem_head _ _).
case: s ih hb=> [|y ys] ih hb; first by rewrite /= expr1.
rewrite nonempty_product_cons //.
apply: le_trans (hsub _ _) _.
rewrite [size (_::_)]/= exprS; apply: ler_pM=> //.
- exact: real_seminorm_nonnegative hN _.
- exact: real_seminorm_nonnegative hN _.
- apply: ih=> z hz; apply: hb; by rewrite in_cons hz orbT.
Qed.

(** Source for [symmetric_one_form_power_finite_bound]: Federer
    1.10.5, p. 47, the upper half of the power-norm identity.
    If every one-form value on a tuple has length at most L, then
    its m-th power on that tuple has length at most m! L^m. *)
Lemma symmetric_one_form_power_finite_bound (R : realType) (V W : lmodType R)
    (N : W -> R) (hN : is_real_seminorm N) (mu : W -> W -> W)
    (hmu : bilinear mu) (hsub : forall x y, N (mu x y)<=N x*N y)
    (f : S_m V W 1) m (hm : (0<m)%N) (t : m.-tuple V) L (hL : 0<=L) :
  (forall i, N (f [tuple tnth t i])<=L) ->
  N (symmetric_one_form_power hmu f m t) <= (m`!)%:R * L^+m.
Proof.
move=> hb; rewrite (symmetric_one_form_power_permutations hmu f hm).
apply: le_trans (real_seminorm_sum hN _) _.
have he : (\sum_(sigma:'S_m) L^+m)=(m`!)%:R*L^+m.
  by rewrite sumr_const card_Sn mulr_natl.
rewrite -he; apply: ler_sum=> sigma _.
have hh := @nonempty_product_seminorm_bound R W N hN mu hsub L hL
  [seq sform_words f [::tnth t (sigma i)] | i<-enum 'I_m].
rewrite size_map size_enum_ord in hh; apply: hh=> z /mapP[i hi ->].
rewrite (sform_wordsE f [tuple tnth t (sigma i)]); exact: hb.
Qed.
