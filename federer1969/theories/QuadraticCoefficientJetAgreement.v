(** Federer (1969), 3.4.5, p. 321: actual finite jets
    of the cleared coefficient operators depend only on the
    corresponding finite jets of the original coefficient fields. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormAnalyticUP NormAnalyticConstant NormAnalyticScalarProducts NormFiniteJetAgreement
  NormFiniteJetScalarProductAgreement NormFiniteJetFiniteSumAgreement
  QuadraticSubstitutionParameterCoefficients ClearedQuadraticSubstitution AnalyticQuadraticCoefficientOperators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Agreement.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable A:set X.
Hypothesis hOpen:forall x,A x ->norm_domain_interior NX A x.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX N hNX hN).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN A f).
Local Notation AG f g m a:=(norm_finite_jet_agreement NX ev NZ A A f g m a).

(** Source for [quadratic_parameter_coefficient_jet_agreement]:
    actual finite agreeing jets give agreeing parameter coefficients,
    by proved finite linear operations, supporting 3.4.5, p. 321. *)
Theorem quadratic_parameter_coefficient_jet_agreement parity order ell
    (f g:nat->nat->X->R) m a:
  A a ->(forall i k,AN (f i k)) ->(forall i k,AN (g i k)) ->
  (forall i k,(i<=order)%N ->(k<=order)%N ->AG (f i k) (g i k) m a) ->
  AG (fun x=>quadratic_substitution_parameter_coefficient parity order ell (fun i k=>f i k x))
     (fun x=>quadratic_substitution_parameter_coefficient parity order ell (fun i k=>g i k x)) m a.
Proof.
move=>ha hf hg hAgree.
pose F (b:nat->nat->X->R) (i k:'I_order.+1) (x:X):=
  if ((ell<=k)&&(i+2*k+parity+ell==order))%N then b i k x*('C(k,ell))%:R*(-1)^+(k-ell) else 0.
have hAN b (hb:forall i k,AN (b i k)) i k:AN (F b i k).
  rewrite /F;case:((ell<=k)&&(i+2*k+parity+ell==order))%N.
  - apply:norm_analytic_scalar_product.
    + apply:norm_analytic_scalar_product;first exact:hb.
      exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
    + exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
  - exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen 0).
have hPoint i k:AG (F f i k) (F g i k) m a.
  rewrite /F;case:((ell<=k)&&(i+2*k+parity+ell==order))%N.
  - apply:norm_finite_jet_analytic_scalar_factor;try exact:ha;try exact:(hAN _ hf i k).
    + apply:norm_analytic_scalar_product;first exact:hf.
      exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
    + apply:norm_analytic_scalar_product;first exact:hg.
      exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
    + exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
    + apply:norm_finite_jet_analytic_scalar_factor;try exact:ha;try exact:hf;try exact:hg.
      * exact:(@norm_constant_analytic R X R^o NX N hNX hN A hOpen _).
      * apply:hAgree;by rewrite -ltnS;apply:ltn_ord.
  - by move=>r hr z;split.
have hRow b (hb:forall i k,AN (b i k)) i:AN (fun x=>\sum_k F b i k x).
  apply:norm_analytic_finite_scalar_sum;[exact:hOpen|move=>k;exact:(hAN b hb i k)].
have hRowAgree i:AG (fun x=>\sum_k F f i k x) (fun x=>\sum_k F g i k x) m a.
  apply:norm_finite_jet_finite_sum_agreement;try exact:ha;try exact:hOpen.
  - exact:(hAN f hf i).
  - exact:(hAN g hg i).
  - exact:hPoint.
have hTotal:=@norm_finite_jet_finite_sum_agreement R X R^o NX N hNX hN A
  (Finite.clone 'I_order.+1 _) (fun i x=>\sum_k F f i k x) (fun i x=>\sum_k F g i k x) m a
  ha hOpen (hRow f hf) (hRow g hg) hRowAgree.
have hValue b x:quadratic_substitution_parameter_coefficient parity order ell (fun i k=>b i k x)=
    \sum_i \sum_k F b i k x.
  rewrite /quadratic_substitution_parameter_coefficient;apply:eq_bigr=>i _.
  by rewrite big_mkcond.
have hFunction b:(fun x=>quadratic_substitution_parameter_coefficient parity order ell (fun i k=>b i k x))=
    (fun x=>\sum_i \sum_k F b i k x).
  by apply:funext=>x;exact:hValue.
by rewrite !hFunction.
Qed.

(** Source for [quadratic_cleared_remainder_jet_agreement]: actual
    finite jets remain equal under the original denominator-cleared
    remainder operator, supporting 3.4.5, p. 321. *)
Theorem quadratic_cleared_remainder_jet_agreement parity order (z c:X->R)
    (f g:nat->nat->X->R) m a:
  A a ->AN z ->AN c ->(forall i k,AN (f i k)) ->(forall i k,AN (g i k)) ->
  (forall i k,(i<=order)%N ->(k<=order)%N ->AG (f i k) (g i k) m a) ->
  AG (fun x=>quadratic_cleared_remainder parity order (z x) (c x) (fun i k=>f i k x))
     (fun x=>quadratic_cleared_remainder parity order (z x) (c x) (fun i k=>g i k x)) m a.
Proof.
move=>ha hz hc hf hg hAgree.
pose W (ell:nat) x:=z x^+(order-ell)*c x^+ell.
have hW ell:AN (W ell).
  apply:norm_analytic_scalar_product;apply:norm_analytic_scalar_power;assumption.
pose B (b:nat->nat->X->R) ell x:=quadratic_substitution_parameter_coefficient parity order ell (fun i k=>b i k x).
have hB b (hb:forall i k,AN (b i k)) ell:AN (B b ell):=
  @quadratic_parameter_coefficient_analytic R X NX hNX A hOpen parity order ell b hb.
have hTerm b (hb:forall i k,AN (b i k)) ell:AN (fun x=>B b ell x*W ell x):=
  norm_analytic_scalar_product (hB b hb ell) (hW ell).
have hTermAgree (ell:'I_order.+1):AG (fun x=>B f ell x*W ell x) (fun x=>B g ell x*W ell x) m a.
  apply:norm_finite_jet_analytic_scalar_factor;try exact:ha;try exact:(hB f hf ell);try exact:(hB g hg ell);try exact:hW.
  exact:(@quadratic_parameter_coefficient_jet_agreement parity order ell f g m a ha hf hg hAgree).
have hTotal:=@norm_finite_jet_finite_sum_agreement R X R^o NX N hNX hN A
  (Finite.clone 'I_order.+1 _) (fun ell x=>B f ell x*W ell x) (fun ell x=>B g ell x*W ell x)
  m a ha hOpen (fun ell=>hTerm f hf ell) (fun ell=>hTerm g hg ell) hTermAgree.
have hValue b x:quadratic_cleared_remainder parity order (z x) (c x) (fun i k=>b i k x)=
    \sum_(ell<order.+1) B b ell x*W ell x.
  rewrite /quadratic_cleared_remainder;apply:eq_bigr=>ell _;exact:mulrC.
have hFunction b:(fun x=>quadratic_cleared_remainder parity order (z x) (c x) (fun i k=>b i k x))=
    (fun x=>\sum_(ell<order.+1) B b ell x*W ell x).
  by apply:funext=>x;exact:hValue.
by rewrite !hFunction.
Qed.
End Agreement.
