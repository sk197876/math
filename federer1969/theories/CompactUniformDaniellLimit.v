(** Federer (1969), 4.1.5, p. 350:
    the scalar Daniell restriction has the
    original compact continuous extension. Reuse
    the fixed-support Daniell bound from 2.5.13
    to pass every common-support uniform
    approximation through the functional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactUniformNorm VectorFunctionLattice
  DaniellIntegralUP DaniellSpaceCompactness CompactDaniellUniformBound PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_uniform_daniell_positive_limit]: the
    compact approximation of a scalar Daniell
    integral in Federer 4.1.5, p. 350.
    One common compact support is enough;
    the whole source need not be compact. *)
Theorem compact_uniform_daniell_positive_limit (R:realType) (X:topologicalType)
    (A:(X->R)->R) (w:X->R) (P:R->X->R) (C:set X) (r:R):
  hausdorff_space X ->locally_compact (@setT X) ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  compactly_supported_continuous_functions w ->compact C ->0<r ->
  (forall e:R,0<e ->compactly_supported_continuous_functions (P e)) ->
  (forall e:R,0<e ->e<r ->forall x,~C x ->P e x=0) ->
  (forall eta:R,0<eta ->exists d:R,0<d /\forall e:R,0<e ->e<d ->forall x,`|P e x-w x|<eta) ->
  @positive_norm_limit R R^o (fun t:R^o=>`|t|) (fun e=>A (P e)) (A w).
Proof.
move=>hHausdorff hLocallyCompact hA hW hC hR hP hZero hUniform eta hEta.
pose K:=C `|` real_function_support w.
have hK:compact K:=compactU hC hW.2.
have[B [hB hBound]]:=@compact_daniell_fixed_support_bound R X A K hHausdorff hLocallyCompact hK hA.
have hBOne:0<B+1 by lra.
pose delta:=eta/(B+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have[d [hD hClose]]:=hUniform delta hDelta.
exists (Num.min r d); split; first by rewrite lt_min hR hD.
move=>e hE hSmall.
have /andP [hER hED]:(e<r)&&(e<d) by move:hSmall; rewrite lt_min.
have hLattice:=@compact_support_vector_lattice R X.
have hError:=@vector_function_lattice_difference R X _ hLattice (P e) w (hP e hE) hW.
have hOff x:~K x ->P e x-w x=0.
  move=>hNot.
  have hNotC:~C x by move=>hx; apply:hNot; by left.
  have hNotW:~real_function_support w x by move=>hx; apply:hNot; by right.
  by rewrite (hZero e hE hER x hNotC) (real_function_zero_off_support hNotW) subrr.
have hDifference:=@vector_lattice_additive_difference R X _ A hLattice (daniell_integral_add hA)
  (P e) w (hP e hE) hW.
have hErrorBound:=hBound (fun x=>P e x-w x) hError hOff delta hDelta
  (fun x _=>ltW (hClose e hE hED x)).
rewrite hDifference in hErrorBound.
apply:le_lt_trans hErrorBound _.
have hStrict:delta*B<delta*(B+1) by rewrite ltr_pM2l // ltrDl ltr01.
by rewrite /delta divfK ?gt_eqF // in hStrict.
Qed.
