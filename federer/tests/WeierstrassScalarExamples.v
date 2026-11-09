(** Federer (1969), 3.4.6, pp. 321–324: actual
    scalar regressions test a nontrivial finite remainder
    and an original leading coefficient different from one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology ring.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticDomain
  NormAnalyticOperations NormAnalyticScalarProducts ScalarPowerAnalytic ScalarAffineAnalytic
  ScalarNormMetricCompleteness AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  WeierstrassRegularUP WeierstrassLineRegularity WeierstrassTransverseUP WeierstrassTransverseSealed
  WeierstrassDivisionUP WeierstrassDivisionSealed WeierstrassPolynomialRepresentative
  WeierstrassPreparationUP WeierstrassPreparationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarExamples.
Variable R:realType.
Let N:=fun t:R^o=>`|t|.
Let hN:=@scalar_absolute_value_norm R.
Let xi:Hom R^o R^o:=hom_of_linear (linear_id R^o).
Let v:R^o:=1.
Let hXi:norm_bounded_linear N N xi.
Proof.
exists 1;split;first exact:ler01.
by move=>x;rewrite /xi hom_of_linearE mul1r.
Qed.
Let hUnit:xi v= 1.
Proof. reflexivity. Qed.
Let K:=@WeierstrassTransverse.space R R^o N hN v xi hXi hUnit.
Let NK:=@WeierstrassTransverse.norm R R^o N hN v xi hXi hUnit.
Let inclusion:=@WeierstrassTransverse.inclusion R R^o N hN v xi hXi hUnit.
Let projection:=@WeierstrassTransverse.projection R R^o N hN v xi hXi hUnit.
Let hSplit:=@WeierstrassTransverse.laws R R^o N hN v xi hXi hUnit.

(** Source for [weierstrass_cubic_division_regression]:
    phi(t)=t^3 and psi(t)=t+1 have actual quotient
    zero and actual remainder t+1, testing existence,
    uniqueness, and all required remainder derivatives
    in 3.4.6(1), p. 322. Every original
    regularity and analytic premise is proved. *)
Example weierstrass_cubic_division_regression:
  exists phi psi:analytic_representative_type hN (0:R^o),
    analytic_representative_value phi=(fun t=>t^+3) /\
    analytic_representative_value psi=(fun t=>t+1) /\
    exists hRegular:is_weierstrass_regular_germ (analytic_germ phi) 3%N v,
      @WeierstrassDivision.quotient R R^o N hN (@scalar_norm_metric_complete R) 3%N v
        (analytic_germ phi) (analytic_germ psi) hRegular=0 /\
      @WeierstrassDivision.remainder R R^o N hN (@scalar_norm_metric_complete R) 3%N v
        (analytic_germ phi) (analytic_germ psi) hRegular=analytic_germ psi.
Proof.
have [phi hPhi]:=@analytic_representative_from_domain R R^o N hN 0 setT (fun t=>t^+3)
  (@scalar_power_analytic_at R 3%N 0).
have hPsiAN:@norm_analytic R R^o R^o N N hN hN setT (fun t=>t+1).
  move=>a _;apply:(@norm_analytic_at_domain_agreement R R^o R^o N N hN hN setT
    (fun t=>1*t+1) (fun t=>t+1) a _ (@scalar_affine_analytic_at R 1 1 a)).
  by move=>t _;rewrite mul1r.
have [psi hPsi]:=@analytic_representative_from_domain R R^o N hN 0 setT (fun t=>t+1) (hPsiAN 0 Logic.I).
have hRegular:@is_weierstrass_regular_germ R R^o N hN (analytic_germ phi) 3%N v.
  apply:(@weierstrass_line_regularity R R^o N hN phi 3%N v 1 (erefl true) (oner_neq0 R))=>t.
  rewrite hPhi /v.
  change ((t*1)^+3= 1*t^+3);by rewrite mulr1 mul1r.
pose C:=fun (i:nat) (_:R^o)=>if ((i==0)||(i==1))%N then (1:R) else 0.
have hPolynomial:@is_directional_polynomial_germ R R^o N hN 3%N v (analytic_germ psi).
  apply:(@weierstrass_polynomial_representative R R^o K N NK hN v xi inclusion projection 3%N C psi hSplit).
  - by rewrite hPsi.
  - rewrite hPsi;apply:funext=>t.
    rewrite /C !big_ord_recl big_ord0 /= /xi ?hom_of_linearE ?expr0 ?expr1.
    ring.
have hCandidate:@is_weierstrass_division R R^o N hN 3%N v
    (analytic_germ phi) (analytic_germ psi) 0 (analytic_germ psi).
  constructor;last exact:hPolynomial.
  by rewrite mul0r add0r.
have [hQ hT]:=@WeierstrassDivision.unique R R^o N hN (@scalar_norm_metric_complete R) 3%N v
  (analytic_germ phi) (analytic_germ psi) hRegular 0 (analytic_germ psi) hCandidate.
exists phi,psi;split;first exact:hPhi.
split;first exact:hPsi.
exists hRegular;split;[exact:esym hQ|exact:esym hT].
Qed.

(** Source for [weierstrass_simple_zero_regression]:
    phi(t)=2t has original nonunit leading coefficient
    and order one, testing scalar normalization and
    complete monic preparation in 3.4.6(2), p. 322.
    No regularity or prepared-factor premise is assumed. *)
Example weierstrass_simple_zero_regression:
  exists phi:analytic_representative_type hN (0:R^o),
    analytic_representative_value phi=(fun t=>2*t) /\
    exists hRegular:is_weierstrass_regular_germ (analytic_germ phi) 1%N v,
      @is_weierstrass_preparation R R^o K N NK hN
        (@WeierstrassTransverse.norm_laws R R^o N hN v xi hXi hUnit) xi projection 1%N (analytic_germ phi)
        (@WeierstrassPreparation.multiplier R R^o N hN v xi hXi hUnit (@scalar_norm_metric_complete R)
          (analytic_germ phi) 1%N hRegular)
        (@WeierstrassPreparation.polynomial R R^o N hN v xi hXi hUnit (@scalar_norm_metric_complete R)
          (analytic_germ phi) 1%N hRegular)
        (@WeierstrassPreparation.coefficients R R^o N hN v xi hXi hUnit (@scalar_norm_metric_complete R)
          (analytic_germ phi) 1%N hRegular).
Proof.
have hPhiAN:@norm_analytic_at R R^o R^o N N hN hN setT (fun t=>2*t) 0.
  apply:(@norm_analytic_at_domain_agreement R R^o R^o N N hN hN setT
    (fun t=>2*t+0) (fun t=>2*t) 0 _ (@scalar_affine_analytic_at R 2 0 0)).
  by move=>t _;rewrite addr0.
have [phi hPhi]:=@analytic_representative_from_domain R R^o N hN 0 setT (fun t=>2*t) hPhiAN.
have hTwo:(2:R)!=0 by rewrite pnatr_eq0.
have hRegular:@is_weierstrass_regular_germ R R^o N hN (analytic_germ phi) 1%N v.
  apply:(@weierstrass_line_regularity R R^o N hN phi 1%N v 2 (erefl true) hTwo)=>t.
  rewrite hPhi /v expr1.
  change (2*(t*1)= 2*t);by rewrite mulr1.
exists phi;split;first exact:hPhi.
exists hRegular.
exact:(@WeierstrassPreparation.laws R R^o N hN v xi hXi hUnit (@scalar_norm_metric_complete R)
  (analytic_germ phi) 1%N hRegular).
Qed.
End ScalarExamples.
