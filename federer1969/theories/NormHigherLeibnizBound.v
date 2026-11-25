(** Federer (1969), 3.1.13, p. 225:
    derivative norm bounds obtained from the general
    Leibniz formula of 3.1.11, p. 222.
    The constants use only the bounds on the
    two families of actual derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import TensorUP Hom BoundedHom Bilinear RealNormUP SymmetricAlgebra SymmetricForms
  SymmetricFormSum SymmetricFormProduct SymmetricOperatorNormUP SymmetricOperatorNorm
  SymmetricProductFiniteBounds ContinuousMultilinearUP NormClassHigherUP
  NormHigherSymmetricFormUP NormHigherLeibniz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_leibniz_form_bound]:
    ||D^i(fg)|| is bounded by the
    sum of binomial(i,i-j) times the
    norms of D^(i-j)f and D^j g.
    This consequence of Federer 3.1.11,
    p. 222, supplies the
    normalization estimates in 3.1.13,
    p. 225. *)
Theorem norm_higher_leibniz_form_bound (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (mu : Y->Y->Y) (hmu : bilinear mu)
    (hM : forall x y, NY (mu x y)<=NY x*NY y)
    (A : X->Prop) (f g : X->Y) k a
    (phi psi : forall i, S_m X Y i) (F G : nat->R) i (eta : S_m X Y i) :
  A a ->
  norm_class_higher NX NY ev ZN A f k ->
  norm_class_higher NX NY ev ZN A g k ->
  (forall j, (j<=k)%N -> is_norm_higher_differential_form NX ev ZN A f j a (phi j)) ->
  (forall j, (j<=k)%N -> is_norm_higher_differential_form NX ev ZN A g j a (psi j)) ->
  (forall j, (j<=k)%N -> (symmetric_operator_norm hNX.1 NY (phi j)<=(F j)%:E)%E) ->
  (forall j, (j<=k)%N -> (symmetric_operator_norm hNX.1 NY (psi j)<=(G j)%:E)%E) ->
  (i<=k)%N ->
  is_norm_higher_differential_form NX ev ZN A (fun x=>mu (f x) (g x)) i a eta ->
  (symmetric_operator_norm hNX.1 NY eta<=
    (\sum_(j<i.+1) ('C(i,i-j))%:R*(F (i-j)%N*G j))%:E)%E.
Proof.
move=>ha hf hg hphi hpsi hF hG hi heta.
have hform := @norm_higher_leibniz R X Y NX NY hNX hNY Z ev ZN hZ
  mu hmu hM A f g k a phi psi ha hf hg hphi hpsi i hi eta heta.
apply: (symmetric_operator_norm_bound hNX.1 NY eta _).2=>t ht.
have he := congr1 (fun H : S_star X Y=>H (symmetric_word t)) hform.
rewrite -sform_componentE sform_includeK hom_finite_sumE in he.
rewrite he; apply: le_trans (real_seminorm_sum hNY.1 _) _.
apply: ler_sum=>j _.
have hj : (j<=i)%N by move:(ltn_ord j); rewrite ltnS.
have hjk := leq_trans hj hi.
have hij := leq_trans (leq_subr j i) hi.
exact (@symmetric_product_included_unit_bound R X Y NX NY hNX hNY mu hmu hM
  (i-j)%N j i (phi (i-j)%N) (psi j) (F (i-j)%N) (G j) t
  (subnK hj) (hF _ hij) (hG _ hjk) ht).
Qed.
