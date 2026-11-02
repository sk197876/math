(** Federer (1969), 3.1.11, pp. 221–222:
    the derivatives through order k of a
    class-k function agree with the Taylor
    coefficients of any polynomial approximation with
    an order-k negligible remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP SymmetricForms HomogeneousPolynomialFunctions
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor PolynomialDiagonalNorm
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialSymmetricForm NormClassHigherUP NormClassHigherFields
  NormTaylorRemainderBound NormTaylorLineValues NormTaylorLineRemainder
  NormLittleOPower PolynomialFiniteOrderComparison PolynomialTaylorExactExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_polynomial_approximation_differentials]:
    coefficient comparison used for the Leibniz
    and composition formulas in Federer 3.1.11,
    p. 222, from the corollary
    on p. 221. The approximating
    polynomial may have degree greater than k;
    only its first k+1 coefficients are identified. *)
Theorem norm_polynomial_approximation_differentials (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (P : PolynomialFunction X Y) :
  A a -> norm_class_higher NX NY ev ZN A f k ->
  (forall v, norm_little_o_power NY (fun t=>f (a+t*:v)-P (a+t*:v)) k) ->
  forall i, (i<=k)%N -> forall z : Z i,
    has_norm_higher_differential NX ev ZN A f i a z ->
    forall u, @ev i u z=polynomial_taylor_coefficient P i a [tuple u j | j<i].
Proof.
move=>ha hf happ i hi z hz.
have [D [hD hc]] := norm_class_higher_fields hNX hNY hZ hf.
have hzi : z=D i a := norm_higher_differential_unique hNX hNY hZ hz (hD i hi a ha).
have [phi [hphi _]] := norm_higher_differential_symmetric_form_exists hNX hNY hZ hz.
have hphieq : phi=polynomial_taylor_coefficient P i a.
  apply: (@sform_polynomial_injective R X Y i (@pchar_num R)).
  apply: funext=>v.
  pose L := maxn k (polynomial_degree P).
  have hkL : (k<=L)%N := leq_maxl _ _.
  have hdegL : (polynomial_degree P<=L)%N := leq_maxr _ _.
  pose c j : Y := if (j<=k)%N then
    ((j`!)%:R)^-1*:@ev j [ffun _ : 'I_j=>v] (D j a) else 0.
  pose d j : Y := sform_polynomial_value (polynomial_taylor_coefficient P j a) v.
  have hec t : norm_taylor_value ev D a (t*:v) k=
      \sum_(j<L.+1) t^+j*:c j.
    rewrite (norm_taylor_value_on_line hZ).
    have hwide : (k.+1<=L.+1)%N by [].
    rewrite (big_ord_widen L.+1
      (fun j=>t^+j*:(((j`!)%:R)^-1*:@ev j [ffun _ : 'I_j=>v] (D j a))) hwide)
      big_mkcond.
    apply: eq_bigr=>j _; rewrite /c ltnS.
    by case:(j<=k)%N; rewrite ?scaler0.
  have hed t : P (a+t*:v)=\sum_(j<L.+1) t^+j*:d j.
    rewrite (@polynomial_taylor_formula_any_higher_order R (@pchar_num R) X Y P L a (t*:v) hdegL).
    apply: eq_bigr=>j _; exact: sform_polynomial_scale_argument.
  have hactual := @norm_taylor_line_little_o_fields R X Y NX NY hNX hNY
    Z ev ZN hZ A f D k a v ha hf.1 hD (hc k (leqnn k)).
  have hco : norm_little_o_power NY
      (fun t=>f (a+t*:v)-\sum_(j<L.+1) t^+j*:c j) k.
    move=>e he; have [r [hr hb]] := hactual e he.
    exists r; split=> // t ht; rewrite -hec; exact: hb.
  have hdo : norm_little_o_power NY
      (fun t=>f (a+t*:v)-\sum_(j<L.+1) t^+j*:d j) k.
    move=>e he; have [r [hr hb]] := happ v e he.
    exists r; split=> // t ht; rewrite -hed; exact: hb.
  have hiL : (i<L.+1)%N by rewrite ltnS; exact: leq_trans hi hkL.
  have hcoeff := finite_power_initial_asymptotic_coefficients_unique hNY hco hdo hi hiL.
  have hcphi : c i=sform_polynomial_value phi v.
    rewrite /c hi sform_polynomial_diagonal_value hphi hzi.
    congr (_*:@ev i _ (D i a)).
    by apply/ffunP=>j; rewrite !ffunE tnth_mktuple.
  by rewrite hcphi in hcoeff.
move=>u.
have hh := hphi [tuple u j | j<i].
have he : [ffun j=>tnth [tuple u l | l<i] j]=u.
  by apply/ffunP=>j; rewrite !ffunE tnth_mktuple.
by rewrite he hphieq in hh.
Qed.
