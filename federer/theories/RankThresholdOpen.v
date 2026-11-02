(** Federer (1969), 3.1.18, p. 229, first display: openness of rank
    superlevel sets, by continuity of exterior powers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra num_normedtype.
From Federer Require Import Hom InnerProductUP InnerNorm InnerMetric RealNormUP
  NormMetric RealMetricBackground NormDifferentialUP NormBoundedLinearTopology NormClassOneUP
  LinearBasis HomInner HomSpaceTopology ExteriorGrading ExteriorMaps
  FiniteExteriorPowers ExteriorNorm ExteriorMapNormContinuity SimpleElementary
  ExteriorHadamardBound IndependentProducts InnerExteriorPositivity
  LinearRankUP LinearRankAtLeast.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RankOpen.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX:X->R) (B:X->X->R) (C:Y->Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable m:nat.
Variable b:'I_m->X.
Hypothesis hb:is_basis b.
Local Notation NY := (inner_norm hC).
Local Notation BX := (inner_norm hB).
Local Notation H := (inner_metric_space (hom_inner_productP hB hC hb)).
Hypothesis hNXeq : NX=BX.
Variables (A:set X) (D:X->Hom X Y).
Hypothesis hA : forall a, A a -> norm_domain_interior NX A a.
Hypothesis hD : norm_field_continuous NX NY A D.

(** Source for [rank_threshold_interior]: the rank threshold has a
    neighbourhood at each of its points, supporting the open-set
    assertion in Federer 3.1.18, p. 229. The proof follows its exterior
    product argument, without a choice of coordinates for D. *)
Lemma rank_threshold_interior a v : A a -> linear_rank_at_least (D a) v ->
  norm_domain_interior NX (fun x=>A x /\ linear_rank_at_least (D x) v) a.
Proof.
move=>ha [e he].
have h2:(1+1:R)!=0 by change (2%:R !=(0:R)); rewrite pnatr_eq0.
pose xi := e_lambda e (ord_tuple v).
have hsimple := product_simple e.
pose F (L:H) : real_line_metric R :=
  exterior_norm h2 hC (exterior_power_map (hom_as_linear (L:Hom X Y)) v xi)^+2.
have hF : continuous F.
  exact (@exterior_map_norm_square_continuous R h2 X Y B C hB hC m b hb v xi hsimple).
have hnz : F (D a)!=0.
  rewrite /F exterior_power_map_e_lambda.
  rewrite expf_eq0 /= exterior_norm_eq0.
  change (e_lambda (fun i=>D a (e i)) (ord_tuple v)!=0).
  exact (@independent_product_nonzero R h2 Y v (fun i=>D a (e i)) he).
have hopen : open [set t:real_line_metric R|t!=0] := @open_neq R 0.
have hnb : nbhs (F (D a)) [set t:real_line_metric R|t!=0].
  apply: open_nbhs_nbhs; by split.
have hpre := hF (D a) _ hnb.
have [r hr hgood] := (@hom_space_nbhs_operator R X Y B C hB hC m b hb (D a) _).1 hpre.
have hhalf:0<r/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hdiff]] := @hD a ha (r/2) hhalf.
have [s [hs hAs]] := @hA a ha.
exists (Num.min d s); split; first by rewrite lt_min hd hs.
move=>z; rewrite lt_min=>/andP [hzd hzs].
have haz := hAs z hzs; split=>//.
exists e; apply: exterior_product_nonzero_independent.
have hop : hom_operator_norm hB hC hb (D (a+z)-D a)<=r/2.
  apply: hom_operator_norm_least; first exact: ltW hhalf.
  move=>u; rewrite -hNXeq; exact: hdiff z haz hzd u.
have hrr : r/2<r by lra.
have hz : F (D (a+z))!=0 := hgood _ (le_lt_trans hop hrr).
rewrite /F exterior_power_map_e_lambda expf_eq0 /= exterior_norm_eq0 in hz.
exact hz.
Qed.

(** Source for [rank_threshold_open]: the first open-set assertion
    of Federer 3.1.18, p. 229. The topology is that of the actual norm
    on the source and the domain is kept explicitly. *)
Theorem rank_threshold_open v :
  @open [the topologicalType of real_norm_metric_space hNX]
    [set x | A x /\ linear_rank_at_least (D x) v].
Proof.
rewrite openE=>a [ha hrank].
exact ((@norm_domain_interior_neighbourhood R X NX hNX
  (fun x=>A x /\ linear_rank_at_least (D x) v) a).1
  (rank_threshold_interior ha hrank)).
Qed.
End RankOpen.
