(** Federer (1969), 3.1.24, p. 240: the scalar
    rational majorant and its explicitly solved quadratic inverse.
    Analyticity of the displayed inverse is proved from the
    actual positive-square-root domain and analytic arithmetic. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal ring.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP NormRegularity
  NormAnalyticUP NormAnalyticLocal NormAnalyticDomain NormAnalyticComposition NormAnalyticArithmetic
  NormAnalyticArithmeticLocal ScalarAffineAnalytic ScalarSquareRootAnalytic ScalarAnalyticFraction
  NormClassZeroPositiveLocus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_inverse_discriminant]: the discriminant
    (x-beta-2)^2-4(beta+1) in the explicit inverse formula,
    Federer 3.1.24, p. 240. *)
Definition scalar_inverse_discriminant (R:realType) (b x:R):R :=
  (x-(b+2))^+2-4*(b+1).

(** Source for [scalar_inverse_majorant_domain]: the open
    positive-discriminant domain on which the square root in
    Federer 3.1.24, p. 240, is real analytic. The
    inverse identities will use its local branch through zero. *)
Definition scalar_inverse_majorant_domain (R:realType) (b x:R) :=
  0<scalar_inverse_discriminant b x.

(** Source for [scalar_inverse_majorant]: the explicit
    scalar inverse f displayed in Federer 3.1.24, p. 240.
    The nonzero denominator for positive beta,gamma is retained
    in subsequent inverse claims. *)
Definition scalar_inverse_majorant (R:realType) (b g x:R):R :=
  (x+b-Num.sqrt (scalar_inverse_discriminant b x))/(2*(b+1)*g).

(** Source for [scalar_forward_majorant]: the scalar g in
    Federer 3.1.24, p. 240, written using the proved
    rational fraction gamma*y/(1-gamma*y). On its actual
    nonzero-denominator domain this equals beta*gamma*y minus
    the positive-degree tail starting with gamma^2*y^2. *)
Definition scalar_forward_majorant (R:realType) (b g y:R):R :=
  (b+1)*g*y-scalar_analytic_fraction g y.

(** Source for [scalar_inverse_discriminant_zero]: the
    discriminant at zero is beta squared, supporting the
    branch through zero in Federer 3.1.24, p. 240. *)
Lemma scalar_inverse_discriminant_zero (R:realType) (b:R) :
  scalar_inverse_discriminant b 0= b^+2.
Proof. rewrite /scalar_inverse_discriminant sub0r sqrrN !expr2; ring. Qed.

(** Source for [scalar_inverse_majorant_zero_domain]: zero
    lies in the positive-discriminant domain when beta>0,
    supporting the scalar inverse in Federer 3.1.24, p. 240. *)
Lemma scalar_inverse_majorant_zero_domain (R:realType) (b:R) :
  0<b -> scalar_inverse_majorant_domain b 0.
Proof. move=>hb; rewrite /scalar_inverse_majorant_domain scalar_inverse_discriminant_zero; exact: exprn_gt0. Qed.

(** Source for [scalar_inverse_majorant_zero]: the explicit
    scalar inverse passes through zero for beta>0,
    Federer 3.1.24, p. 240. *)
Lemma scalar_inverse_majorant_zero (R:realType) (b g:R) :
  0<b -> scalar_inverse_majorant b g 0=0.
Proof.
move=>hb; rewrite /scalar_inverse_majorant scalar_inverse_discriminant_zero sqrtr_sqr
  (ger0_norm (ltW hb)) add0r subrr mul0r; reflexivity.
Qed.

(** Source for [scalar_inverse_majorant_analytic_at]: the
    displayed quadratic inverse is analytic on its actual
    positive-discriminant domain, as asserted in Federer
    3.1.24, p. 240. Its numerator is an affine map
    minus the composition of the positive square root with a
    polynomial; the denominator is a fixed scalar. *)
Theorem scalar_inverse_majorant_analytic_at (R:realType) (b g a:R) :
  scalar_inverse_majorant_domain b a ->
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
    (scalar_inverse_majorant_domain b) (scalar_inverse_majorant b g) a.
Proof.
move=>ha.
pose hN:=scalar_absolute_value_norm R.
pose Q:=scalar_inverse_discriminant b.
pose D:=scalar_inverse_majorant_domain b.
have hQ x:@norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN setT Q x.
  exact (@scalar_shifted_square_analytic_at R (b+2) (4*(b+1)) x).
have hQa:@norm_analytic R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN setT Q.
  by move=>x _; exact (hQ x).
have hQ0:norm_class_zero (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) setT Q.
  exact (norm_analytic_class_all_orders hQa 0%N).1.
have hDopen x (hx:D x):norm_domain_interior (fun t:R^o=>`|t|) D x.
  have [r [hr hb]]:=@norm_class_zero_positive_locus_interior R R^o (fun t=>`|t|) hN
    setT Q hQ0 x Logic.I hx.
  exists r; split; first exact hr; by move=>v hv; exact (hb v hv).2.
have hRoot:=@norm_analytic_at_composition R R^o R^o R^o
  (fun t=>`|t|) (fun t=>`|t|) (fun t=>`|t|) hN hN hN setT (fun t=>0<t)
  Q Num.sqrt a (hQ a) (@scalar_square_root_analytic_at R (Q a) ha).
have hRootD:=@norm_analytic_at_domain_enlargement R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  (fun x=>setT x /\ 0<Q x) D (fun x=>Num.sqrt (Q x)) a (fun x hx=>hx.2) hRoot.
have hAff:=@scalar_affine_analytic_at R 1 b a.
have hAffLocal:=@norm_analytic_at_open_restriction R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  setT D (fun x=>1*x+b) a ha hDopen hAff.
have hAffD:=@norm_analytic_at_domain_enlargement R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  (fun x=>setT x /\ D x) D (fun x=>1*x+b) a (fun x hx=>hx.2) hAffLocal.
have hSub:=@norm_analytic_at_subtract R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN D
  (fun x=>1*x+b) (fun x=>Num.sqrt (Q x)) a hAffD hRootD.
have hScale:=@norm_analytic_at_scale R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN D
  (fun x=>1*x+b-Num.sqrt (Q x)) a ((2*(b+1)*g)^-1) hSub.
apply: (@norm_analytic_at_domain_agreement R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  D (fun x=>(2*(b+1)*g)^-1*:(1*x+b-Num.sqrt (Q x))) (scalar_inverse_majorant b g) a _ hScale).
move=>x hx; rewrite /scalar_inverse_majorant mul1r.
change ((2*(b+1)*g)^-1*(x+b-Num.sqrt (Q x))=
  (x+b-Num.sqrt (Q x))*(2*(b+1)*g)^-1); exact: mulrC.
Qed.

(** Source for [scalar_inverse_majorant_analytic_zero]: the
    particular scalar inverse used to majorize all inverse
    derivatives is analytic at zero, Federer 3.1.24,
    p. 240. Positive beta and gamma are those of the
    printed construction. Its recurrence identification is separate. *)
Theorem scalar_inverse_majorant_analytic_zero (R:realType) (b g:R) :
  0<b -> 0<g ->
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
    (scalar_inverse_majorant_domain b) (scalar_inverse_majorant b g) 0.
Proof.
move=>hb hg; exact (@scalar_inverse_majorant_analytic_at R b g 0 (scalar_inverse_majorant_zero_domain hb)).
Qed.
