(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the
    original all-order factorial-growth subsets are closed. The narrow
    num_normedtype import supplies closed scalar order rays as
    background topology; the germ argument is proved here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology num_normedtype.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP NormMetric RealMetricBackground NormMetricContinuity
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermMetric HolomorphicGermJetContinuity
  HolomorphicGermGrowthUP HolomorphicGermGrowthSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_growth_class_closed]: each
    subset displayed in 3.4.5, p. 319, is
    closed for the original exact metric. Every actual jet
    coordinate and its norm are continuous; intersect the
    closed coordinate bounds in all orders, including zero. *)
Theorem holomorphic_germ_growth_class_closed (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) s t:
  @closed (@holomorphic_germ_metric R X NX hNX a)
    (@HolomorphicGermGrowth.value R X NX hNX a s t).
Proof.
pose M:=@holomorphic_germ_metric R X NX hNX a.
have hClasses:=@HolomorphicGermGrowth.laws R X NX hNX a s t.
have hEquation:(@HolomorphicGermGrowth.value R X NX hNX a s t:set M)=
    \bigcap_(m in @setT nat) [set alpha:M|holomorphic_germ_jet_norm m alpha<=s%:R*t%:R^+m*(m`!)%:R].
  apply/seteqP;split=>alpha hAlpha.
  - move=>m _;exact:((holomorphic_germ_growth_membership hClasses alpha).1 hAlpha m).
  - apply/(holomorphic_germ_growth_membership hClasses alpha)=>m;exact:hAlpha m Logic.I.
rewrite hEquation;apply:closed_bigI=>m _.
pose N:=@ContinuousMultilinear.norm R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
  (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)).
pose Y:=real_norm_metric_space hN.
pose f:=fun alpha:M=>(@HolomorphicGermJets.value R X NX hNX a m alpha:Y).
have hf:continuous f:=@holomorphic_germ_jet_continuous R X NX hNX a m.
have hNorm:continuous (fun z:Y=>(N z:real_line_metric R)).
  exact:(@real_norm_metric_norm_continuous R _ N hN).
change (closed ((fun alpha:M=>(N (f alpha):real_line_metric R)) @^-1`
  [set z:real_line_metric R|z<=s%:R*t%:R^+m*(m`!)%:R])).
apply:preimage_closed;last exact:closed_le.
move=>alpha _;exact:continuous_comp (hf alpha) (hNorm (f alpha)).
Qed.
