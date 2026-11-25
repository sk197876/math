(** Federer (1969), 4.1.5, p. 350: the original
    continuous compact norm-tail cutoff exists. Its
    quotient witness vanishes on a whole small-norm
    neighbourhood, which proves continuity at zero norm.
    The quotient is used only in this existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology num_normedtype lra.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricContinuity CompactSupportFunctionUP
  CompactContinuousVectorFields CompactNormTailUP NormTailScalarLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_norm_tail_cutoff_exists]:
    the h in K(U)+ chosen for the two convolution
    estimates in Federer 4.1.5, p. 350. The whole
    cutoff support lies in the original norm support. *)
Theorem compact_norm_tail_cutoff_exists (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (w:X->Y) eta:
  compact_continuous_vector_fields hNY w ->0<eta ->
  exists h:X->R,is_compact_norm_tail_cutoff NY w eta h.
Proof.
move=>hw hEta.
pose f x:=NY (w x).
have hF:=compact_continuous_vector_field_norm hw.
pose h x:=Num.max (f x-eta) 0/f x.
have hLaws x:=@norm_tail_scalar_ratio_laws R (f x) eta
  (real_seminorm_nonnegative hNY.1 (w x)) hEta.
have hSmall x:f x<eta ->h x=0:= (hLaws x).2.2.1.
have hSupport:@real_function_support R X h `<=` @real_function_support R X f.
  apply:(@real_function_support_in_closed_set R X h _ (@real_function_support_closed R X f))=>x hx.
  apply:hSmall; by rewrite (@real_function_zero_off_support R X f x hx).
exists h; constructor.
- split.
  + move=>x; case:(eqVneq (f x) 0)=>[hx|hx].
    * have hxSmall:f x<eta by rewrite hx.
      have hAt:h x=0:=hSmall x hxSmall.
      have hNear:nbhs (f x:real_line_metric R) [set t|t<eta].
        apply:open_nbhs_nbhs; split; first exact:open_lt.
        exact hxSmall.
      have hControl:=hF.1 x _ hNear.
      move=>A hA; rewrite hAt in hA.
      apply:(@filterS _ _ (nbhs_filter _) _ _ _ hControl)=>y hy.
      change (A (h y)); rewrite (hSmall y hy); exact:nbhs_singleton hA.
    * have hNumerator:continuous (fun y:X=>(Num.max (f y-eta) 0:real_line_metric R)).
        move=>y; apply:(@continuous_max R X (fun z=>f z-eta) (fun _=>0) y); last exact:cvg_cst.
        apply:(@continuousB R R^o X f (fun _=>eta) y); first exact:hF.1 y.
        exact:cvg_cst.
      apply:(@continuousM R X (fun y=>Num.max (f y-eta) 0) (fun y=>(f y)^-1) x).
      -- exact:hNumerator x.
      -- apply:(@continuousV R X f x)=>//; exact:hF.1 x.
  + exact:(@subclosed_compact X _ _ (@real_function_support_closed R X h) hw.2 hSupport).
- move=>x; exact:(hLaws x).1.
- move=>x; exact:(hLaws x).2.1.
- exact hSmall.
- exact hSupport.
Qed.
