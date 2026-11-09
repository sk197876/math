(** Federer (1969), 3.4.4, p. 318: the
    constant jets satisfy the full hypothesis of Whitney's theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP SymmetricForms SymmetricFormZero
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor WhitneyModulusUP
  SymmetricOperatorNormUP SymmetricOperatorNorm ExtendedSupremumUP
  RealPower HolderPowerCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatJets.
Variable R:realType.
Variable m:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable P:X->PolynomialFunction (R_n R m) Y.
Variable phi:X->Y.
Hypothesis hZero:forall a x,polynomial_taylor_coefficient (P a) 0 x=zero_sform (R_n R m) (phi a).
Hypothesis hPositive:forall a i x,polynomial_taylor_coefficient (P a) i.+1 x=0.

(** Source for [flat_whitney_zero_difference_bound]: the
    only possibly nonzero term of the constant-jet Whitney
    modulus in 3.4.4, p. 318. Its operator
    norm is bounded by the actual difference of the values. *)
Lemma flat_whitney_zero_difference_bound a b:
  (@whitney_difference_norm R m Y NY P 0 a b<=(NY (phi a-phi b))%:E)%E.
Proof.
rewrite /whitney_difference_norm !hZero.
apply/symmetric_operator_norm_bound=>t ht.
change (is_true (NY ((zero_sform (R_n R m) (phi a)-zero_sform (R_n R m) (phi b)) t)<=NY (phi a-phi b))).
by rewrite -linearB zero_sformE.
Qed.

(** Source for [flat_whitney_positive_difference_bound]: all
    positive-order terms of the actual Whitney modulus vanish
    for the jets of 3.4.4, p. 318. *)
Lemma flat_whitney_positive_difference_bound i a b:
  (@whitney_difference_norm R m Y NY P i.+1 a b<=0)%E.
Proof.
rewrite /whitney_difference_norm !hPositive subrr.
apply/symmetric_operator_norm_bound=>t ht.
by rewrite sform_zeroE (real_seminorm_zero hNY.1).
Qed.

(** Source for [flat_whitney_holder_jet_family]: application
    of 3.1.14 in 3.4.4, p. 318.
    A Holder exponent strictly greater than the natural
    order k makes every compact-set Whitney modulus tend
    to zero. The proof retains the printed factorial,
    actual operator norms, and all positive cutoffs. *)
Theorem flat_whitney_holder_jet_family (A:set X) k (C p:R):
  closed A ->0<C ->k%:R<p ->
  (forall a,polynomial_degree (P a)=0%N) ->
  (forall a b,A a ->A b ->NY (phi a-phi b)<=C*real_power (N (a-b)) p) ->
  is_whitney_jet_family NY k P A.
Proof.
move=>hA hC hP hDegree hHolder.
split=>//;split.
- move=>a ha;by rewrite hDegree leq0n.
- move=>D hDA hCompact e he.
  have hFactor:0<((k`!)%:R:R) by rewrite ltr0n fact_gt0.
  have hCoefficient:0<C*(k`!)%:R:=mulr_gt0 hC hFactor.
  have hExponent:0<p-k%:R by rewrite subr_gt0.
  have [delta [hDelta hCutoff]]:=holder_positive_power_cutoff hCoefficient hExponent he.
  exists delta;split=>// d hd hdDelta.
  apply:(extended_supremum_least (@whitney_modulusP R m Y NY k P D d)).
  move=>r [[i [a [b [q [hi [ha [hb [hDistance [hSmall [hNorm hValue]]]]]]]]]]|->].
  + have haA:=hDA a ha.
    have hbA:=hDA b hb.
    subst r.
    case:i hi hNorm=>[|i] hi hNorm.
    * have hQ:(q<=NY (phi a-phi b)).
        have h:=flat_whitney_zero_difference_bound a b.
        by rewrite hNorm lee_fin in h.
      have hBound:=le_trans hQ (hHolder a b haA hbA).
      have hInverse:0<=(N (a-b))^-(k) by rewrite invr_ge0 exprn_ge0 //;exact:ltW hDistance.
      have hFirst:=ler_wpM2r hInverse hBound.
      have hSecond:=ler_wpM2r (ltW hFactor) hFirst.
      rewrite subn0.
      have hReorder:(C*real_power (N (a-b)) p)*(N (a-b))^-(k)*(k`!)%:R=
          (C*(k`!)%:R)*(real_power (N (a-b)) p*(N (a-b))^-(k)) by ring.
      rewrite hReorder (@holder_power_natural_quotient R (N (a-b)) p k hDistance) in hSecond.
      have hSmallDelta:N (a-b)<=delta:=le_trans hSmall hdDelta.
      have hFinal:=hCutoff (N (a-b)) (ltW hDistance) hSmallDelta.
      rewrite lee_fin;exact:le_trans hSecond hFinal.
    * have hQ:(q<=0).
        have h:=flat_whitney_positive_difference_bound i a b.
        by rewrite hNorm lee_fin in h.
      have hInverse:0<=(N (a-b))^-(k-i.+1) by rewrite invr_ge0 exprn_ge0 //;exact:ltW hDistance.
      have hFacNonnegative:0<=((((k-i.+1)%N)`!)%:R:R) by rewrite ler0n.
      have hFirst:=ler_wpM2r hInverse hQ.
      have hSecond:=ler_wpM2r hFacNonnegative hFirst.
      rewrite !mul0r in hSecond.
      rewrite lee_fin;exact:le_trans hSecond (ltW he).
  + by rewrite lee_fin;exact:ltW he.
Qed.
End FlatJets.
