(** Federer (1969), 3.4.8(11), p. 333:
    a full-dimensional analytic germ is the whole
    germ. An original nonzero equation vanishing on
    beta cuts out an empty or strictly smaller
    exceptional variety. These assertions use the
    proved nonzero-ideal depth bound and original
    ideal separation, before the stratification induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws AnalyticGermRepresentatives
  CommutativeIdealUP SetGermUP SetGermSealed SetGermOrder SetGermBoundary AnalyticVarietyGermUP
  GermVanishingSealed GermVanishingIdeal AnalyticIdealPropriety AnalyticProperVarietyNonzeroIdeal
  AnalyticDepthSealed AnalyticNonzeroIdealDepth AnalyticZeroGermSealed AnalyticZeroGermIdeal
  AnalyticZeroGermVarieties.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FullDimensionalCut.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n.+1->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n.+1->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n.+1 e he omega).
Local Notation zero:=(@AnalyticZeroGerm.value R X NX hNX 0).

(** Source for [analytic_full_dimensional_variety_whole]:
    alpha=gamma_0(R^m) in the original n=m
    case of 3.4.8(11), p. 333.
    A proper analytic germ would have a
    nonzero proper ideal and hence strictly smaller depth. *)
Lemma analytic_full_dimensional_variety_whole (alpha:@set_germ_space T 0):
  @is_analytic_variety_germ R X NX hNX 0 alpha ->alpha<>germ set0 ->
  depth (ideal alpha) = n.+1 ->alpha = germ setT.
Proof.
move=>hAlpha hNonempty hDepth;apply:contrapT=>hProper.
have hIProper:~ideal alpha (1:A).
  move=>hUnit;apply:hNonempty;exact:(analytic_set_ideal_contains_one alpha).1 hUnit.
have [phi [hPhi hNonzero]]:=analytic_proper_variety_nonzero_ideal hAlpha hProper.
have hDrop:=@analytic_nonzero_proper_ideal_depth_lt R X B hB n e he hON omega hDual
  (ideal alpha) (analytic_set_ideal_ring_laws alpha) hIProper (ex_intro _ phi (conj hPhi hNonzero)).
by move:hDrop;rewrite hDepth ltnn.
Qed.

(** Source for [analytic_nonzero_equation_depth_drop]:
    the zero variety of the original nonzero
    equation has depth below the full source
    dimension, as used in 3.4.8(11), p. 333.
    The zero germ is treated separately. *)
Lemma analytic_nonzero_equation_depth_drop (phi:A):
  phi<>0 ->zero phi = germ set0 \/(depth (ideal (zero phi))<n.+1)%N.
Proof.
move=>hNonzero;case:(pselect (zero phi = germ set0))=>hEmpty;first by left.
right.
have hProper:~ideal (zero phi) (1:A).
  move=>hUnit;apply:hEmpty;exact:(analytic_set_ideal_contains_one _).1 hUnit.
have hPhi:ideal (zero phi) phi.
  apply:(@analytic_zero_germ_ideal_equivalence R X NX hNX 0 (zero phi) phi).2.
  exact:set_germ_subset_reflexive.
exact:(@analytic_nonzero_proper_ideal_depth_lt R X B hB n e he hON omega hDual
  (ideal (zero phi)) (analytic_set_ideal_ring_laws _) hProper (ex_intro _ phi (conj hPhi hNonzero))).
Qed.

(** Source for [analytic_full_dimensional_exceptional_equation]:
    choose the actual Phi vanishing on beta,
    with gamma_0(Phi) nonzero, in the full
    source-dimensional case of 3.4.8(11), p. 333.
    Its original zero germ contains beta and
    has the strict dimension drop required for induction. *)
Theorem analytic_full_dimensional_exceptional_equation (beta:@set_germ_space T 0):
  @is_analytic_variety_germ R X NX hNX 0 beta ->beta<>germ setT ->
  exists f:@analytic_representative_type R X NX hNX 0,
    analytic_germ f<>(0:A) /\ideal beta (analytic_germ f) /\
    set_germ_subset beta (zero (analytic_germ f)) /\
    (zero (analytic_germ f) = germ set0 \/(depth (ideal (zero (analytic_germ f)))<n.+1)%N).
Proof.
move=>hBeta hProper.
have [phi [hPhi hNonzero]]:=analytic_proper_variety_nonzero_ideal hBeta hProper.
have [f hF]:=@analytic_germ_has_representative R X NX hNX 0 phi.
exists f;rewrite hF;split;first exact:hNonzero.
split;first exact:hPhi.
split.
- exact:(@analytic_zero_germ_ideal_equivalence R X NX hNX 0 beta phi).1 hPhi.
- exact:analytic_nonzero_equation_depth_drop hNonzero.
Qed.
End FullDimensionalCut.
