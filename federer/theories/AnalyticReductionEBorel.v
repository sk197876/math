(** Federer (1969), 3.4.8(5), p. 328:
    the exact E_m equations preserve Borelness
    under the original finite intersections and
    complements. This supporting implication uses the
    independent reduction-locus laws; actual A, B and
    C Borelness is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticReductionLociUP
  BorelFamilyBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_E_borel_from_membership]:
    the original E_m is C_m intersected with all
    B_j for j>m, minus A_m; E_n is the
    complement of A_n, as in 3.4.8(2),(5),
    pp. 326, 328. This proves only the
    finite Borel-family step, including n=0. *)
Theorem analytic_reduction_E_borel_from_membership (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (O:topologicalType)
  (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
  (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
  (rotated:O->set (@analytic_germ_ring R X NX hNX 0))
  (A:'I_n.+1->set O) (B C:'I_n->set O) (E:'I_n.+1->set O):
  is_analytic_reduction_loci e gamma Q rotated A B C E ->
  (forall j,borel_set (A j)) ->(forall j,borel_set (B j)) ->
  (forall j,borel_set (C j)) ->forall j,borel_set (E j).
Proof.
move=>hLaws hA hB hC j.
case hCase:(j<n)%N.
- pose m:'I_n:=Ordinal hCase.
  have hIndex:j = widen_ord (leqnSn n) m by apply:val_inj.
  pose D:set 'I_n:=fun k=>(m<=k)%N.
  pose H:set O:=fun g=>forall k:'I_n,(m<=k)%N ->B k g.
  have hH:borel_set H.
    change (borel_set (\bigcap_(k in D) B k)).
    apply:(@borel_set_countable_intersection O (Choice.clone 'I_n _) D B).
    + exact:(finite_set_countable (@finite_finset (Finite.clone 'I_n _) D)).
    + exists m;exact:leqnn.
    + by move=>k _;exact:hB k.
  have hSame:E j = (C m `&` H) `\` A j.
    apply/seteqP;split=>g.
    + rewrite hIndex;move/(analytic_reduction_E_membership hLaws m g)=>[hCm [hAll hNot]].
      by split;first split.
    + move=>[[hCm hAll] hNot];rewrite hIndex in hNot *.
      apply/(analytic_reduction_E_membership hLaws m g);by split=>//;split.
  rewrite hSame;apply:borel_set_difference;last exact:hA j.
  exact:(borel_family_binary_intersection (borel_sets_family O) (hC m) hH).
- have hValue:(j:nat) = n.
    have hUpper:(j<=n)%N:=ltn_ord j.
    have hLower:(n<=j)%N by rewrite leqNgt hCase.
    apply/eqP;by rewrite eqn_leq hUpper hLower.
  have hIndex:j = ord_max by apply:val_inj.
  have hSame:E j = ~` A j.
    rewrite hIndex;apply/seteqP;split=>g.
    + exact:(analytic_reduction_E_last_membership hLaws g).1.
    + exact:(analytic_reduction_E_last_membership hLaws g).2.
  rewrite hSame;exact:borel_set_complement (hA j).
Qed.
