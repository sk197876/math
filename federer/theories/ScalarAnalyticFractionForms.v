(** Federer (1969), 3.1.24, p. 239: symmetric
    forms of the actual derivatives of the rational scalar
    functions in the composition calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom RealNormUP SymmetricForms SymmetricFunctionalProduct
  ContinuousMultilinearUP ContinuousMultilinearZero NormHigherDifferentialUP NormHigherSymmetricFormUP
  ScalarAnalyticFraction ScalarAnalyticFractionDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_analytic_fraction_form_actual]: the
    actual differential of cx/(1-cx) at zero is the
    symmetric form c^j j! times the product form in
    positive orders, Federer 3.1.24, p. 239.
    The zeroth form is zero. This theorem packages the
    previously proved recursive differential field calculation
    for use in the general composition formula of 3.1.11. *)
Lemma scalar_analytic_fraction_form_actual (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun x:R^o=>`|x|) (fun x:R^o=>`|x|)
      (@ev i) (@ZN i)) c j :
  is_norm_higher_differential_form (fun x:R^o=>`|x|) ev ZN
    (scalar_analytic_fraction_domain c) (scalar_analytic_fraction c) j 0
    (scalar_analytic_fraction_form c j).
Proof.
have [_ [D [hD he]]]:=scalar_analytic_fraction_differentials hZ c.
have hzero:=scalar_analytic_fraction_zero_domain c.
exists (D j 0); split; first exact (hD j 0 hzero).
case:j=>[|j] u.
- have hh:=(hD 0%N 0 hzero).2.
  rewrite scalar_analytic_fraction_zero in hh.
  rewrite (zero_arity_arguments_unique u [ffun i:'I_0=>(0:R^o)]).
  rewrite hh /scalar_analytic_fraction_form sform_zeroE; reflexivity.
- rewrite (he j.+1 (leq0n j)) /scalar_analytic_fraction_form sform_scaleE
    symmetric_functional_product_formE.
  change ((\prod_(i<j.+1) u i)*(c^+j.+1*((j.+1)`!)%:R)=
    (c^+j.+1*((j.+1)`!)%:R)*\prod_(i<j.+1) tnth [tuple u l | l<j.+1] i).
  have ht:(\prod_(i<j.+1) tnth [tuple u l | l<j.+1] i)= \prod_(i<j.+1) u i.
    by apply: eq_bigr=>i _; rewrite tnth_mktuple.
  by rewrite ht mulrC.
Qed.
