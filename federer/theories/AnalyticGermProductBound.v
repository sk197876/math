(** Federer (1969), 3.4.5, p. 319: the
    actual derivative coordinates of a germ product satisfy
    the finite Leibniz norm bound of 3.1.11, p. 222.
    This proves, rather than assumes, the estimate used
    for continuity of multiplication. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal ring.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations NormLinearDomainLaws
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherSymmetricFormUP NormHigherLeibnizBound
  SymmetricForms SymmetricOperatorNorm AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed AnalyticGermRingLaws
  AnalyticGermGrowthUP AnalyticGermJetsSealed AnalyticGermCoefficientForms AnalyticGermFormActual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_product_jet_bound]: the
    actual m-th product derivative is bounded by the
    original finite binomial Leibniz sum, 3.1.11,
    p. 222, used for the ring topology of 3.4.5,
    p. 319. All orders, including zero, remain. *)
Theorem analytic_germ_product_jet_bound (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m (alpha beta:analytic_germ_space hNX a):
  @analytic_germ_jet_norm R X NX hNX a m (@AnalyticGerms.mul R X NX hNX a alpha beta)<=
    \sum_(j<m.+1) ('C(m,m-j))%:R*
      (@analytic_germ_jet_norm R X NX hNX a (m-j)%N alpha*@analytic_germ_jet_norm R X NX hNX a j beta).
Proof.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX NS hNX hNS.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX NS hNX hNS.
pose N i:=@ContinuousMultilinear.norm R i X R^o NX NS hNX hNS.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
have [U [c [haU [hUT [hClassF hBoundF]]]]]:=analytic_representative_analytic f.
have [V [d [haV [hVT [hClassG hBoundG]]]]]:=analytic_representative_analytic g.
pose W:=U `&` V.
have ha:W a by split.
have hOpen x (hx:W x):norm_domain_interior NX W x.
  exact:norm_domain_intersection_interior ((hClassF 0%N).1 x hx.1).1 ((hClassG 0%N).1 x hx.2).1.
have hF:=@norm_class_open_restriction R X R^o NX NS hNX hNS U W (analytic_representative_value f) m
  (fun x hx=>hx.1) hOpen (hClassF m).
have hG:=@norm_class_open_restriction R X R^o NX NS hNX hNS V W (analytic_representative_value g) m
  (fun x hx=>hx.2) hOpen (hClassG m).
have [phi [hPhi [hPhiBound hPhiNorm]]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a alpha.
have [psi [hPsi [hPsiBound hPsiNorm]]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a beta.
pose gamma:=@AnalyticGerms.mul R X NX hNX a alpha beta.
have [eta [hEta [hEtaBound hEtaNorm]]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a gamma.
have hActualPhi j:is_norm_higher_differential_form NX ev N W (analytic_representative_value f) j a (phi j).
  exact:(@analytic_germ_coefficient_actual_on_neighbourhood R X NX hNX a j alpha f W (phi j) hf ha hOpen (hPhi j)).
have hActualPsi j:is_norm_higher_differential_form NX ev N W (analytic_representative_value g) j a (psi j).
  exact:(@analytic_germ_coefficient_actual_on_neighbourhood R X NX hNX a j beta g W (psi j) hg ha hOpen (hPsi j)).
pose p:=@analytic_multiply_representatives R X NX hNX a f g.
have hRep:analytic_germ p=gamma.
  by rewrite /gamma -hf -hg (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
have hActualEta:=@analytic_germ_coefficient_actual_on_neighbourhood R X NX hNX a m gamma p W (eta m)
  hRep ha hOpen (hEta m).
have hMul:bilinear (fun x y:R^o=>x*y).
  split.
  - move=>x b y z;change ((b*y+z)*x=b*(y*x)+z*x);ring.
  - move=>x b y z;change (x*(b*y+z)=b*(x*y)+x*z);ring.
have hMulBound x y:NS (x*y)<=NS x*NS y by rewrite /NS normrM.
have hPhiLe j:(symmetric_operator_norm hNX.1 NS (phi j)<=
    (@analytic_germ_jet_norm R X NX hNX a j alpha)%:E)%E by rewrite hPhiNorm.
have hPsiLe j:(symmetric_operator_norm hNX.1 NS (psi j)<=
    (@analytic_germ_jet_norm R X NX hNX a j beta)%:E)%E by rewrite hPsiNorm.
have hBound:=@norm_higher_leibniz_form_bound R X R^o NX NS hNX hNS Z ev N hZ
  (fun x y=>x*y) hMul hMulBound W (analytic_representative_value f) (analytic_representative_value g)
  m a phi psi (fun i=>@analytic_germ_jet_norm R X NX hNX a i alpha)
  (fun i=>@analytic_germ_jet_norm R X NX hNX a i beta) m (eta m)
  ha hF hG (fun j _=>hActualPhi j) (fun j _=>hActualPsi j)
  (fun j _=>hPhiLe j)
  (fun j _=>hPsiLe j) (leqnn m) hActualEta.
by rewrite hEtaNorm lee_fin in hBound.
Qed.
