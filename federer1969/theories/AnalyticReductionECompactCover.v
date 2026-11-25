(** Federer (1969), 3.4.8(5), p. 328, auxiliary proof sentence:
    the original E_m is a countable union of compact sets for every
    proper ideal. Arbitrary-ideal index comparison reduces to minimum
    depth, where the proved exclusion removes A_m. No difference law
    for countable compact unions is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology
  HilbertFormCompactness LinearBasis OrthonormalFamilies OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  TopologicalGroupUP AnalyticGermRing CommutativeIdealUP AnalyticReductionActual AnalyticReductionLociUP
  AnalyticDepthSealed AnalyticArbitraryIdealReductionIndex AnalyticMinimumTailExclusion
  IncreasingCompactCoverUP IncreasingCompactCoverIntersections AnalyticReductionABCCompactCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_actual_E_compact_cover]: the
    stronger auxiliary sentence in the proof of Federer 3.4.8(5),
    p. 328. Every original E_m is sigma compact for an arbitrary
    original proper ideal. Empty, zero and full indices are included;
    neither primeness nor a vanishing-ideal representation is assumed. *)
Theorem analytic_reduction_actual_E_compact_cover (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)) (m:'I_n.+1):
  is_commutative_ideal I ->~I 1 ->
  exists K:nat->set (@orthogonal_group R X B hB n e he),
    is_increasing_compact_cover (@analytic_reduction_actual_E R X B hB n e he omega I m) K.
Proof.
move=>hI hProper.
pose O:=@orthogonal_group R X B hB n e he.
pose E:=@analytic_reduction_actual_E R X B hB n e he omega I.
pose Btail:=@analytic_reduction_actual_B R X B hB n e he omega I.
pose C:=@analytic_reduction_actual_C R X B hB n e he omega I.
have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
change (exists K:nat->set O,is_increasing_compact_cover (E m) K).
have hCompact:@compact O setT:=@orthogonal_group_compact_space R X B hB n e he.
have hHausdorff:hausdorff_space O.
  have [mul [inv [unit hGroup]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
  exact:(lch_group_hausdorff (@orthogonal_group_lch R X B hB n e he mul inv unit hGroup)).
case:(pselect (@AnalyticDepth.value R X B hB n e he omega I = (m:nat)))=>hDepth.
- case:(ltnP m n)=>hLess.
  + pose j:'I_n:=Ordinal hLess.
    have hIndex:widen_ord (leqnSn n) j = m by apply:val_inj.
    pose H:set O:=fun g=>forall k:'I_n,(j<=k)%N ->Btail k g.
    have hSame:E m = C j `&` H.
      apply/seteqP;split=>g.
      * rewrite -hIndex;move/(analytic_reduction_E_membership hLoci j g)=>[hC [hT _]].
        by split.
      * move=>[hC hT];rewrite -hIndex;apply/(analytic_reduction_E_membership hLoci j g).
        split;first exact:hC.
        split;first exact:hT.
        rewrite hIndex.
        exact:(@analytic_minimum_tail_excludes_A R X B hB n e he hON omega hDual I m g
          hI hProper hDepth hT).
    have [KC hKC]:=@analytic_reduction_actual_C_compact_cover R X B hB n e he omega hDual I hI j.
    have hEach k:exists K:nat->set O,is_increasing_compact_cover (Btail k) K.
      exact:(@analytic_reduction_actual_B_compact_cover R X B hB n e he omega hDual I hI k).
    have [KB hKB]:=choice hEach.
    pose KT t:set O:=fun g=>forall k:'I_n,(j<=k)%N ->KB k t g.
    have hKT:is_increasing_compact_cover H KT:=
      @increasing_compact_cover_finite_intersection O (Finite.clone 'I_n _)
        [set k|(j<=k)%N] Btail KB hCompact hHausdorff hKB.
    rewrite hSame;exists (fun t=>KC t `&` KT t);constructor.
    * move=>t;apply:compact_closedI.
      -- exact:increasing_compact_cover_compact hKC t.
      -- apply:compact_closed;first exact:hHausdorff.
         exact:increasing_compact_cover_compact hKT t.
    * move=>t g [hC hT];split.
      -- exact:(increasing_compact_cover_contained hKC hC).
      -- exact:(increasing_compact_cover_contained hKT hT).
    * move=>s t hST g [hC hT];split.
      -- exact:(increasing_compact_cover_monotone hKC hST hC).
      -- exact:(increasing_compact_cover_monotone hKT hST hT).
    * move=>g [hC hT].
      have [s hS]:=increasing_compact_cover_covers hKC hC.
      have [t hMemberT]:=increasing_compact_cover_covers hKT hT.
      exists (maxn s t);split.
      -- exact:(increasing_compact_cover_monotone hKC (leq_maxl s t) hS).
      -- exact:(increasing_compact_cover_monotone hKT (leq_maxr s t) hMemberT).
  + have hEqual:(m:nat) = n by apply/eqP;rewrite eqn_leq hLess andbT;exact:ltn_ord m.
    have hIndex:m = ord_max by apply:val_inj.
    have hSame:E m = setT.
      apply/seteqP;split=>g;first by [].
      move=>_;rewrite hIndex;apply/(analytic_reduction_E_last_membership hLoci g).
      have hTail (k:'I_n):(m<=k)%N ->Btail k g.
        rewrite hEqual=>hK.
        have hBad:=leq_ltn_trans hK (ltn_ord k);by rewrite ltnn in hBad.
      have hNot:=@analytic_minimum_tail_excludes_A R X B hB n e he hON omega hDual I m g
        hI hProper hDepth hTail.
      by rewrite hIndex in hNot.
    rewrite hSame;exists (fun _=>setT);constructor.
    * by move=>_.
    * by move=>t g hG.
    * by move=>s t hST g hG.
    * move=>g _;by exists 0%N.
- have hEmpty:E m = set0.
    apply/seteqP;split=>g;last by [].
    move=>hEm;apply:hDepth.
    exact:(@analytic_arbitrary_ideal_reduction_index R X B hB n e he hON omega hDual I m g hI hProper hEm).
  rewrite hEmpty;exists (fun _=>set0);constructor.
  + move=>_;exact:compact0.
  + by move=>t g [].
  + by move=>s t hST g [].
  + by move=>g [].
Qed.
