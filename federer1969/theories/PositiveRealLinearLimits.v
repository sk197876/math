(** Federer (1969), 4.1.5, pp. 349–350: linearity
    and bounds pass to the original positive-scale scalar
    convolution limits. The algebraic limit laws reuse
    the earlier punctured real limit theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP PositiveNormLimitUP RealCurveDerivativeUP
  PuncturedRealLinearLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PositiveRealLinearLimits.
Variable R:realType.
Local Notation P := (@positive_norm_limit R R^o (fun t:R^o=>`|t|)).

(** Source for [positive_real_limit_absolute_parameter]:
    the original positive-epsilon limit in Federer 4.1.5,
    p. 349, expressed with the existing two-sided scalar
    limit by taking the absolute value of the parameter. *)
Lemma positive_real_limit_absolute_parameter (u:R->R) a:
  P u a <->punctured_real_limit (fun t=>u (`|t|)) a.
Proof.
split.
- move=>h eta hEta; have[d [hd hBound]]:=h eta hEta.
  exists d; split=>// t /andP [ht htd]; exact:hBound `|t| ht htd.
- move=>h eta hEta; have[d [hd hBound]]:=h eta hEta.
  exists d; split=>// t ht htd.
  have hAbs:0<`|t|<d by rewrite (ger0_norm (ltW ht)); apply/andP; split.
  have hb:=hBound t hAbs; by rewrite (ger0_norm (ltW ht)) in hb.
Qed.

(** Source for [positive_real_limit_add]: addition in the
    convolution-limit definition of T, Federer 4.1.5,
    p. 349. The original test evaluations have finite
    scalar limits. *)
Lemma positive_real_limit_add (u v:R->R) a b:
  P u a ->P v b ->P (fun e=>u e+v e) (a+b).
Proof.
move=>hu hv; apply:((@positive_real_limit_absolute_parameter (fun e=>u e+v e) (a+b)).2).
exact:punctured_real_limit_add
  ((@positive_real_limit_absolute_parameter u a).1 hu)
  ((@positive_real_limit_absolute_parameter v b).1 hv).
Qed.

(** Source for [positive_real_limit_scale]: homogeneity in
    the convolution-limit definition of T, Federer 4.1.5,
    p. 349. The zero scalar requires no exception. *)
Lemma positive_real_limit_scale (u:R->R) a c:
  P u a ->P (fun e=>c*u e) (c*a).
Proof.
move=>hu; apply:((@positive_real_limit_absolute_parameter (fun e=>c*u e) (c*a)).2).
exact:punctured_real_limit_scale c ((@positive_real_limit_absolute_parameter u a).1 hu).
Qed.

(** Source for [positive_real_limit_absolute]: absolute
    evaluation bounds pass to the convolution limit in
    Federer 4.1.5, pp. 349–350, by the reverse triangle
    inequality. *)
Lemma positive_real_limit_absolute (u:R->R) a:
  P u a ->P (fun e=>`|u e|) `|a|.
Proof.
move=>hu eta hEta; have[d [hd hBound]]:=hu eta hEta.
exists d; split=>// e he hed.
exact:le_lt_trans (ler_dist_dist _ _) (hBound e he hed).
Qed.

(** Source for [positive_real_limit_eventual_upper]:
    an eventual upper bound survives the original scalar
    limit in Federer 4.1.5, pp. 349–350. A positive
    scale below both cutoffs yields the closed inequality. *)
Lemma positive_real_limit_eventual_upper (u:R->R) a b:
  P u a ->(exists r:R,0<r /\ forall e:R,0<e ->e<r ->u e<=b) ->a<=b.
Proof.
move=>hu [r [hr hUpper]].
rewrite leNgt; apply/negP=>hba.
pose eta:=(a-b)/2.
have hEta:0<eta by rewrite /eta divr_gt0 // ?subr_gt0 // ltr0n.
have[d [hd hBound]]:=hu eta hEta.
pose e:=Num.min r d/2.
have hMin:0<Num.min r d by rewrite lt_min hr hd.
have he:0<e by rewrite /e divr_gt0 // ltr0n.
have hSmall:e<Num.min r d by rewrite /e; lra.
have /andP [her hed]:(e<r)&&(e<d) by rewrite -lt_min.
have hU:=hUpper e he her.
have hB:=hBound e he hed.
move:hB; rewrite ltr_norml=>/andP [hLower _].
have hBad:a<a by rewrite /eta in hLower; lra.
by rewrite ltxx in hBad.
Qed.

(** Source for [positive_real_limit_eventual_absolute_bound]:
    the absolute form of the finite bound for the extended
    T in Federer 4.1.5, pp. 349–350. *)
Lemma positive_real_limit_eventual_absolute_bound (u:R->R) a b:
  P u a ->(exists r:R,0<r /\ forall e:R,0<e ->e<r ->`|u e|<=b) ->`|a|<=b.
Proof.
move=>hu hBound.
exact:positive_real_limit_eventual_upper (positive_real_limit_absolute hu) hBound.
Qed.
End PositiveRealLinearLimits.
