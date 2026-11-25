(** Federer (1969), 3.4.8(14), pp. 328, 336:
    the actual dimension of a finite irreducible union
    is the maximum of the component dimensions. The
    product theorem gives the upper inequality; original
    germ containment gives the lower inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermOrder SetGermFiniteUnion
  GermVanishingSealed AnalyticIrreducibleGermUP AnalyticDepthSealed AnalyticFiniteIrreducibleDepthBound
  AnalyticIdealDepthMonotonicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Maximum.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T 0).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_finite_irreducible_union_depth_maximum]: the
    finite maximum formula in 3.4.8(14), pp. 328, 336.
    Lists may repeat components; maximality is not needed
    for this stronger finite irreducible union statement. *)
Theorem analytic_finite_irreducible_union_depth_maximum (F:seq G):
  F<>[::] ->
  (forall beta,beta \in F ->@is_nonempty_irreducible_analytic_germ R X NX hNX 0 beta) ->
  depth (ideal (@set_germ_finite_union T 0 F))=\max_(beta<-F) depth (ideal beta).
Proof.
move=>hNonempty hIrreducible.
apply/eqP;rewrite eqn_leq;apply/andP;split.
- apply:(@analytic_finite_irreducible_union_depth_bound R n F _ hNonempty hIrreducible).
  move=>beta hBeta;apply:leq_bigmax_seq;first exact:hBeta;exact:isT.
- apply/bigmax_leqP_seq=>beta hBeta _.
  exact:(@analytic_variety_ideal_depth_monotone R X B hB n e he omega beta
    (@set_germ_finite_union T 0 F) (@set_germ_finite_union_member T 0 F beta hBeta)).
Qed.
End Maximum.
