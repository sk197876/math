(** Federer (1969), 3.1.11, p. 220:
    the actual kth differential of inversion is
    the sum of the k! ordered inverse
    products. The proof identifies the coefficients
    of the finite inverse expansion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp fingroup perm reals topology lra ring.
From Federer Require Import Hom AlgebraUP AlgebraGeometricSum AlgebraInverseUP
  AlgebraInverse PartialFunctionUP RealNormUP NormMetric CompleteMetricUP NormDifferentialUP
  NormAlgebraInverseOpen NormAlgebraInverseSmooth AlgebraInverseFiniteRemainder
  AlgebraInverseDifferentialForms ContinuousMultilinearUP FiniteArgumentPermutation NormHigherDifferentialUP
  NormHigherDifferentialUnique NormHigherDifferentialRadialIdentification
  NormTaylorRemainderBound NormTaylorLineValues NormLittleOPower NormLittleOHigherPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section InverseDifferentials.
Variable R : realType.
Variable A : algebra R.
Variable N : A->R.
Hypothesis hN : is_real_norm N.
Hypothesis hM : forall x y, N (alg_mul A x y)<=N x*N y.
Hypothesis hcomplete : is_complete_metric_space (real_norm_metric_space hN).
Variable Z : nat->lmodType R.
Variable ev : forall k, {ffun 'I_k->A}->Hom (Z k) A.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space N N (@ev k) (@ZN k).
Variable F : A->A.
Hypothesis hF : forall x, partial_function_domain (algebra_inverse A) x ->
  is_two_sided_algebra_inverse x (F x).
Local Notation U := (partial_function_domain (algebra_inverse A)).

(** Source for [inverse_form_taylor_value]:
    the divided diagonal of the permutation
    forms gives exactly the finite inverse
    sum, Federer 3.1.11, p. 220. *)
Lemma inverse_form_taylor_value v (phi : forall i, Z i) :
  (forall i u, @ev i u (phi i)=inverse_differential_form v u) ->
  forall a h k,
    norm_taylor_value ev (fun i _=>phi i) a h k=
      alg_mul A (algebra_geometric_sum (-alg_mul A v h) k.+1) v.
Proof.
move=>hphi a h k.
pose Mr := @HomMap R A A (fun y=>alg_mul A y v)
  (introT (asboolP _) ((alg_bilinear A).1 v)).
have he : alg_mul A (algebra_geometric_sum (-alg_mul A v h) k.+1) v=
    \sum_(i<k.+1) alg_mul A
      (@AlgebraPowers.algebra_power R A (-alg_mul A v h) i) v.
  change (Mr (\sum_(i<k.+1) @AlgebraPowers.algebra_power R A (-alg_mul A v h) i)=\sum_(i<k.+1) Mr (@AlgebraPowers.algebra_power R A (-alg_mul A v h) i)).
  exact: linear_sum.
rewrite he /norm_taylor_value; apply: eq_bigr=>i _.
rewrite hphi inverse_differential_form_diagonal scalerA.
have hfpos : (0:R)<(i`!)%:R by rewrite ltr0n fact_gt0.
have hn : ((i`!)%:R : R)!= 0 by rewrite gt_eqF.
by rewrite mulVf // scale1r.
Qed.

(** Source for [inverse_form_radial_remainder]:
    the finite inverse expansion has a
    linewise remainder negligible at every fixed
    Taylor order, supporting the permutation
    differential formula in Federer 3.1.11,
    p. 220 and the identification
    principle on p. 221. *)
Lemma inverse_form_radial_remainder x (phi : forall i, Z i) k :
  U x ->
  (forall i u, @ev i u (phi i)=inverse_differential_form (F x) u) ->
  forall q, norm_little_o_power N
    (fun t=>F (x+t*:q)-norm_taylor_value ev (fun i _=>phi i) x (t*:q) k) k.
Proof.
move=>hx hphi q.
pose C := N (F x)+1.
have hNv := real_seminorm_nonnegative hN.1 (F x).
have hC : 0<C by rewrite /C; lra.
have hCv : N (F x)<=C by rewrite /C; lra.
have [r [hr hball]] := @norm_algebra_inverse_domain_interior R A N hN hM hcomplete x (F x) (@hF x hx).
have hp : 0<1/(2*C) by rewrite divr_gt0 // mulr_gt0 // ltr0n.
have hmin : 0<Num.min r (1/(2*C)) by rewrite lt_min hr hp.
have [d [hd hdq]] := norm_scalar_line_small_increments hN q hmin;
pose B := (C*N q)^+k.+1*(2*C).
have hB : 0<=B.
  apply: mulr_ge0.
  - exact: exprn_ge0 _ (mulr_ge0 (ltW hC) (real_seminorm_nonnegative hN.1 q)).
  - exact: mulr_ge0 (ler0n R 2) (ltW hC).
apply: (@norm_little_o_from_higher_power R A N
  (fun t=>F (x+t*:q)-norm_taylor_value ev (fun i _=>phi i) x (t*:q) k)
  k B d hB hd)=>t /andP [ht0 ht].
have hsmall := hdq t ht.
have /andP [htr htc] : (N (t*:q)<r)&&(N (t*:q)<1/(2*C)).
  by rewrite -lt_min.
have hdom := hball (t*:q) htr.
have hs : 2*C*N (t*:q)<= 1.
  have hh : N (t*:q)*(2*C)<1.
    by move:htc; rewrite ltr_pdivlMr // mulr_gt0 // ltr0n.
  rewrite mulrC; exact: ltW hh.
rewrite (inverse_form_taylor_value hphi).
have hb := norm_algebra_inverse_finite_remainder_bound hN hM
  k.+1 (@hF x hx) (@hF _ hdom) hC hCv hs.
have he : (C*N (t*:q))^+k.+1*(2*C)=B*`|t|^+k.+1.
  rewrite (real_seminorm_scale hN.1) /B !exprMn; ring.
by rewrite he in hb.
Qed.

(** Source for [norm_algebra_inverse_higher_differential_exists]:
    the kth differential of inversion has
    precisely the permutation formula printed
    in Federer 3.1.11, p. 220,
    with degree zero interpreted as inversion itself. *)
Theorem norm_algebra_inverse_higher_differential_exists x k :
  U x -> exists z : Z k,
    has_norm_higher_differential N ev ZN U F k x z /\
    forall u, @ev k u z=inverse_differential_form (F x) u.
Proof.
move=>hx.
have hex i : exists z : Z i,
    forall u, @ev i u z=inverse_differential_form (F x) u.
  exact (@inverse_differential_form_representable R A N hN hM (F x) i
    (Z i) (@ev i) (@ZN i) (@hZ i)).
pose phi i := projT1 (cid (hex i)).
have hphi i u : @ev i u (phi i)=inverse_differential_form (F x) u.
  exact: projT2 (cid (hex i)) u.
have hc := @norm_algebra_inverse_class_infinity R A N hN hM hcomplete Z ev ZN hZ F hF k.
have hsym i (hi : (i<=k)%N) s u :
    @ev i (finite_argument_permutation s u) (phi i)=@ev i u (phi i).
  by rewrite !hphi inverse_differential_form_symmetric.
have hd := @norm_higher_differential_from_radial_expansion R A A N N hN hN
  Z ev ZN hZ U F k x phi hx hc hsym
  (inverse_form_radial_remainder k hx hphi) k (leqnn k).
exists (phi k); split; first exact hd; exact: hphi.
Qed.

(** Source for [norm_algebra_inverse_higher_differential_formula]:
    evaluation of any actual differential
    of inversion by the printed permutation
    sum, Federer 3.1.11, p. 220. *)
Corollary norm_algebra_inverse_higher_differential_formula x k (z : Z k) :
  U x -> has_norm_higher_differential N ev ZN U F k x z ->
  forall u, @ev k u z=inverse_differential_form (F x) u.
Proof.
move=>hx hz; have [w [hw he]] := norm_algebra_inverse_higher_differential_exists k hx.
have -> : z=w := norm_higher_differential_unique hN hN hZ hz hw.
exact he.
Qed.
End InverseDifferentials.
