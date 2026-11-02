(** Federer (1969), 3.1.11, p. 222:
    the general Leibniz formula in the symmetric
    form algebra, proved by multiplying jets and
    comparing their coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom BoundedHom Bilinear RealNormUP SymmetricForms SymmetricFormSum
  SymmetricFormProduct SymmetricPolynomialProduct PolynomialTaylor SymmetricTaylorProducts
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherSymmetricFormUP
  NormClassHigherUP NormJetUP NormJetSealed NormJetLineRemainder
  NormPolynomialApproximationDifferentials NormJetProductDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Leibniz.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable mu : Y->Y->Y.
Hypothesis hmu : bilinear mu.
Hypothesis hM : forall x y, NY (mu x y)<=NY x*NY y.
Variables (A : X->Prop) (f g : X->Y) (k : nat) (a : X).
Variables phi psi : forall i, S_m X Y i.

(** Source for [norm_higher_leibniz]:
    D^i(f g)(a)=sum_(j= 0)^i
    D^(i-j)f(a) odot D^j g(a),
    Federer 3.1.11, p. 222.
    The forms are included in the graded
    symmetric algebra, exactly as in the
    printed notation. Multiplication need not commute. *)
Theorem norm_higher_leibniz :
  A a ->
  norm_class_higher NX NY ev ZN A f k ->
  norm_class_higher NX NY ev ZN A g k ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ev ZN A f i a (phi i)) ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ev ZN A g i a (psi i)) ->
  forall i, (i<=k)%N -> forall eta : S_m X Y i,
    is_norm_higher_differential_form NX ev ZN A (fun x=>mu (f x) (g x)) i a eta ->
    sform_include eta=
      \sum_(j<i.+1) symmetric_forms_product hmu
        (sform_include (phi (i-j))) (sform_include (psi j)).
Proof.
move=>ha hf hg hphi hpsi i hi eta [z [hz hze]].
have [zf [hzf _]] := hphi k (leqnn k).
have [zg [hzg _]] := hpsi k (leqnn k).
pose P := @NormJet.value R X Y NX NY hNX hNY Z ev ZN hZ A f k a zf hzf.
pose Q := @NormJet.value R X Y NX NY hNX hNY Z ev ZN hZ A g k a zg hzg.
have hP := @NormJet.laws R X Y NX NY hNX hNY Z ev ZN hZ A f k a zf hzf.
have hQ := @NormJet.laws R X Y NX NY hNX hNY Z ev ZN hZ A g k a zg hzg.
have hfO := norm_jet_line_little_o hNX hNY hZ ha hf hP.
have hgO := norm_jet_line_little_o hNX hNY hZ ha hg hQ.
have hpc j (hj : (j<=k)%N) : phi j=polynomial_taylor_coefficient P j a.
  have [w [hw hew]] := hphi j hj.
  have hc := @norm_polynomial_approximation_differentials R X Y NX NY hNX hNY
    Z ev ZN hZ A f k a P ha hf hfO j hj w hw.
  apply: symmetric_form_finite_family_extensional=>u; rewrite -hew; exact: hc.
have hqc j (hj : (j<=k)%N) : psi j=polynomial_taylor_coefficient Q j a.
  have [w [hw hew]] := hpsi j hj.
  have hc := @norm_polynomial_approximation_differentials R X Y NX NY hNX hNY
    Z ev ZN hZ A g k a Q ha hg hgO j hj w hw.
  apply: symmetric_form_finite_family_extensional=>u; rewrite -hew; exact: hc.
have heta : eta=polynomial_taylor_coefficient (polynomial_product hmu P Q) i a.
  have hc := @norm_product_jet_differential_coefficients R X Y NX NY hNX hNY
    Z ev ZN hZ mu hmu hM A f g k a P Q ha hf hg hP hQ i z hi hz.
  apply: symmetric_form_finite_family_extensional=>u; rewrite -hze; exact: hc.
rewrite heta (polynomial_taylor_product_coefficients (@pchar_num R)).
apply: eq_bigr=>j _.
have hj : (j<=i)%N by move:(ltn_ord j); rewrite ltnS.
have hjk := leq_trans hj hi.
have hsub := leq_trans (leq_subr j i) hi.
by rewrite (hpc _ hsub) (hqc _ hjk).
Qed.
End Leibniz.
