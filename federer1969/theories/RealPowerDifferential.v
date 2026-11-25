(** Federer (1969), 3.2.13, p. 250: real-power
    differentiation supporting integration by parts for Euler
    Gamma. Derive it from the project's opaque exp/log
    laws and proved actual differentials, on positive bases. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialArithmetic NormDifferentialChain
  NormDifferentialLocal NormDifferentialLocalAgreement RealLogarithmDifferential RealExponentialDifferential
  RealExponentialUP RealExponentialSealed RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_power_linear_term]: the linear
    derivative coefficient p a^(p-1) used for the
    Gamma recurrence, Federer 3.2.13, p. 250. *)
Definition real_power_linear_term (R:realType) (p a:R):Hom R^o R^o.
Proof.
apply:(@HomMap R R^o R^o (fun h=>(p*real_power a (p-1))*h)).
apply/asboolP=>c x y; change ((p*real_power a (p-1))*(c*x+y)=
  c*((p*real_power a (p-1))*x)+(p*real_power a (p-1))*y); ring.
Defined.

(** Source for [real_power_differential]: the real-power
    derivative underlying integration by parts in Federer
    3.2.13, p. 250. Any real exponent is
    admitted, and positivity is required only at the
    point of differentiation, without assuming behavior at zero. *)
Theorem real_power_differential (R:realType) (p a:R):
  0<a ->has_norm_differential (fun r:R^o=>`|r|) (fun r:R^o=>`|r|) setT
    (fun x:R^o=>(real_power x p:R^o)) a (real_power_linear_term p a).
Proof.
move=>ha.
pose hN:=@scalar_absolute_value_norm R.
pose E:=@RealExponential.exponential R.
pose L:=@RealExponential.logarithm R.
pose F:=fun x:R^o=>(E (p*L x):R^o).
have hLog:=real_logarithm_differential ha.
have hScale:=@norm_differential_scale R R^o R^o _ _ hN hN setT L a
  (real_logarithm_linear_term a) p hLog.
have hExp:=@real_exponential_differential R (p*L a).
have hChain:=norm_differential_chain hN hN hN hScale hExp.
have hWhole:norm_domain_interior (fun r:R^o=>`|r|) setT a.
  exists 1; split; first exact:ltr01; by move=>h hh.
have hF:=norm_differential_restrict (fun x _=>conj Logic.I Logic.I) hWhole hChain.
have hEq:hom_comp (real_exponential_linear_term (p*L a))
    (p*:real_logarithm_linear_term a) = real_power_linear_term p a.
  apply:hom_ext=>h.
  change (E (p*L a)*(p*(a^-1*h))=(p*real_power a (p-1))*h).
  have hPower:=@real_power_add_exponents_positive R a (p-1) 1 ha.
  rewrite subrK (real_power_one_exponent (ltW ha)) in hPower.
  have hValue:E (p*L a) = real_power a (p-1)*a.
    rewrite -hPower; exact:Logic.eq_sym (real_power_positive_base p ha).
  rewrite hValue.
  have hArrange:(real_power a (p-1)*a)*(p*(a^-1*h))=
      (p*real_power a (p-1))*(a*a^-1)*h by ring.
  by rewrite hArrange mulfV ?(gt_eqF ha) // mulr1.
rewrite hEq in hF.
have hRadius:0<a/2 by apply:divr_gt0=> //; lra.
apply:(@norm_differential_local_agreement R R^o R^o _ _ hN setT setT F
  (fun x=>real_power x p) a (real_power_linear_term p a) (a/2) hRadius _ _ hF).
- by move=>h hh; split.
- move=>h hSmall _.
  have hLower:=ler_norm (-h); rewrite normrN in hLower.
  have hPositive:0<a+h by nra.
  exact:Logic.eq_sym (real_power_positive_base p hPositive).
Qed.
