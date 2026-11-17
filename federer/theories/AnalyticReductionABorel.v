(** Federer (1969), 3.4.8(5), p. 328:
    every original A_j is Borel, including A_0 empty.
    Actual rotated ideals and actual closed prefix subrings
    enter the compact-projection proof; no Borel premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing AnalyticGermMetric
  CommutativeIdealUP TopologicalBorel AnalyticPrefixGermSubring AnalyticRotatedGermIdeal
  AnalyticRotatedPrefixIncidenceBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_A_borel]: the original
    A_j in 3.4.8(2),(5), pp. 326, 328, is
    Borel for every legal prefix. A_0 retains its
    printed empty-set definition. *)
Theorem analytic_reduction_A_borel
    (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
    n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k)=if i==k then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    j (hjn:(j<=n)%N):
  is_commutative_ideal I ->
  borel_set [set g:@orthogonal_group R X B hB n e he|(0<j)%N /\exists beta,
    @analytic_rotated_germ_ideal R X B hB n e he I g beta /\
    @analytic_prefix_germ_subring R X (inner_norm hB) (inner_norm_real_norm hB)
      n e he omega j hjn beta /\beta<>0].
Proof.
move=>hI.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose M:=@analytic_germ_metric R X NX hNX 0.
pose O:=@orthogonal_group R X B hB n e he.
pose Q:=@analytic_prefix_germ_subring R X NX hNX n e he omega j hjn.
case hPositive:(0<j)%N.
- have hNonzero:@open M (~` [set (0:@analytic_germ_ring R X NX hNX 0)]).
    apply:closed_openC;apply:accessible_closed_set1;apply:hausdorff_accessible;exact:metric_hausdorff.
  have hResult:=@analytic_rotated_prefix_open_incidence_borel R X B hB n e he omega hDual
    I j hjn (~` [set (0:@analytic_germ_ring R X NX hNX 0)]) hI hNonzero.
  have hSame:[set g:O|(0<j)%N /\exists beta,
      @analytic_rotated_germ_ideal R X B hB n e he I g beta /\Q beta /\beta<>0]=
    [set g:O|exists beta,@analytic_rotated_germ_ideal R X B hB n e he I g beta /\Q beta /\beta<>0].
    apply/seteqP;split.
    + by move=>g [_ h].
    + by move=>g h;split;first rewrite hPositive.
  rewrite hPositive in hSame.
  rewrite hSame;exact:hResult.
- have hEmpty:[set g:O|(0<j)%N /\exists beta,
      @analytic_rotated_germ_ideal R X B hB n e he I g beta /\Q beta /\beta<>0]=set0.
    apply/seteqP;split=>g;last by [].
    by move=>[hj _];rewrite hPositive in hj.
  rewrite hPositive in hEmpty.
  rewrite hEmpty;apply:open_borel_set;exact:open0.
Qed.
