(** Federer (1969), 3.2.13, p. 250: continuity
    of the Gamma recurrence integrand on the
    positive open domain, in the project's intrinsic
    class-zero convention used by its fundamental theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import RealMetricBackground RealNormUP NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_positive_continuity_class_zero]: a
    supporting topology adapter for integration by parts
    in Federer 3.2.13, p. 250. Continuity
    at each positive point supplies the intrinsic
    class-zero law on the positive open ray. *)
Lemma scalar_positive_continuity_class_zero (R:realType) (f:R->R):
  (forall a:R,0<a ->(fun x:real_line_metric R=>(f x:real_line_metric R))
    @ (a:real_line_metric R) -->(f a:real_line_metric R)) ->
  norm_class_zero (fun r:R^o=>`|r|) (fun r:R^o=>`|r|) (fun r=>0<r) f.
Proof.
move=>hf a ha; split.
- exists (a/2); split; first by apply:divr_gt0=>//; lra.
  move=>h hh; have hLo:=ler_norm (-h); rewrite normrN in hLo; lra.
- move=>e he.
  have hTarget:nbhs (f a:real_line_metric R) [set y:real_line_metric R | `|f a-y|<e].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP (f a:real_line_metric R) _)).
    exists e; first exact he.
    by move=>y hy.
  have hPre:=hf a ha _ hTarget.
  have [d hd hBound]:=proj1 (metricType_numDomainType.nbhs_mdistP (a:real_line_metric R) _) hPre.
  exists d; split=>// h _ hh.
  have hSmall:mdist (a:real_line_metric R) (a+h)<d.
    by rewrite real_line_metric_distanceE opprD addrA subrr add0r normrN.
  have hValue:=hBound (a+h) hSmall.
  rewrite -[f (a+h)-f a]opprB normrN; exact hValue.
Qed.
