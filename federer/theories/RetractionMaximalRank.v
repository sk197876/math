(** Federer (1969), 3.1.20, p. 233: maximal derivative rank
    is constant on the connected retract, and every point of B
    is generic of that rank. Closedness uses the discrete trace
    values of idempotent derivatives instead of exterior norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm RealNormUP HilbertFormCompactness NormMetric NormDifferentialUP NormClassOneUP
  NormClassZeroTopology NormBoundedLinearTopology NormRegularity RetractionUP NormRetractionDifferential
  LinearRankUP LinearRankAtLeast LinearRankImageInclusion RankThresholdOpen NormRankZero
  EuclideanMaximalRankUP TraceDefinition TraceIdempotentRank EuclideanTraceContinuity
  ContinuousAtClosureValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [connected_retraction_generic_rank]: the maximal
    rank mu and the open-and-closed argument on B in Federer
    3.1.20, p. 233. The trace of an idempotent equals its rank,
    giving the same rank separation without an additional
    hypothesis about the derivative field. *)
Theorem connected_retraction_generic_rank (R:realType) n k
    (A B:set (R_n R n)) (f:R_n R n->R_n R n)
    (D:R_n R n->Hom (R_n R n) (R_n R n)) :
  @connected [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] B ->
  is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R n)) A B f k ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) A f D ->
  (exists a,A a) -> exists mu,(mu<=n)%N /\
    forall b,B b -> norm_generic_rank (inner_norm (@euclidean_inner_productP R n)) A D b mu.
Proof.
move=>hB hR hD hne.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have [mu [hmun [[a [ha hra]] hmax]]]:=euclidean_maximal_rank_exists D hne.
have hExact x (hx:A x):linear_rank_at_least (D x) mu <-> has_linear_rank (D x) mu.
  split.
  - move=>ht; have [r [hr hrn]]:=linear_rank_exists (D x) (@coordinate_basisP R n).
    have hmr: (mu<=r)%N:=(linear_rank_at_leastP mu hr).1 ht.
    have hrm: (r<=mu)%N:=hmax x r hx hr.
    have he:r=mu by apply/eqP; rewrite eqn_leq hrm hmr.
    by rewrite -he.
  - move=>hr; exact: (linear_rank_at_leastP mu hr).2 (leqnn mu).
pose G:=fun x=>A x /\ linear_rank_at_least (D x) mu.
have hA x (hx:A x):norm_domain_interior NX A x:=(norm_class_one_zero hD hx).1.
have hGo:@open [the topologicalType of real_norm_metric_space hNX] G.
  exact (@rank_threshold_open R X X NX (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) hNX (@euclidean_inner_productP R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
    erefl A D hA (norm_class_one_continuity hD) mu).
have hfaB:=@norm_retraction_range R X NX hNX A B f k hR a ha.
have hfaA:=@norm_retraction_subset R X NX hNX A B f k hR (f a) hfaB.
have [s [hs hsn]]:=linear_rank_exists (D (f a)) (@coordinate_basisP R n).
have hmus: (mu<=s)%N.
  apply: (linear_rank_image_inclusion hra hs)=>v.
  exact (@norm_retraction_differential_image R X NX hNX A B f D k hR hD a ha
    (D a v) (ex_intro _ v erefl)).
have hsmu: (s<=mu)%N:=hmax (f a) s hfaA hs.
have heq:s=mu by apply/eqP; rewrite eqn_leq hsmu hmus.
have hfaG:G (f a) by split=>//; apply: (hExact _ hfaA).2; by rewrite -heq.
have hSG:(B `&` G) !=set0 by exists (f a).
have h2:(1+1:R)!=0 by change (2%:R !=(0:R)); rewrite pnatr_eq0.
pose tr:=fun x=>@trace_Hom R h2 X (Finite.clone 'I_n _) (@coordinate_basis R n)
  (@coordinate_basisP R n) (D x).
have htr:=@euclidean_trace_field_continuous R h2 n A f D hD.
have htrank b (hb:B b) r (hr:has_linear_rank (D b) r):tr b=r%:R.
  exact (@idempotent_trace_rank R h2 X n (@coordinate_basis R n) (@coordinate_basisP R n)
    (D b) r hr (@norm_retraction_differential_idempotent R X NX hNX A B f D k hR hD b hb)).
have hSval x (hx:(B `&` G) x):tr x=mu%:R.
  exact (@htrank x hx.1 mu ((hExact x hx.2.1).1 hx.2.2)).
pose ClS:=@closure [the topologicalType of real_norm_metric_space hNX] (B `&` G).
have hClosedRep:(B `&` G)=B `&` ClS.
  apply/seteqP; split=>b.
  - move=>hb; split; [exact hb.1|exact: subset_closure hb].
  - move=>[hb hcl]; split=>//.
    have hbA:=@norm_retraction_subset R X NX hNX A B f k hR b hb.
    have hc:=@norm_class_zero_continuous_at R X R^o NX (fun t:R^o=>`|t|) hNX
      (scalar_absolute_value_norm R) A tr b htr hbA.
    pose Y:=real_norm_metric_space (scalar_absolute_value_norm R).
    have hclosed:@closed [the topologicalType of Y] [set (mu%:R:R^o)].
      exact (@compact_closed Y _ (@metric_hausdorff R Y) (@compact_set1 Y (mu%:R:R^o))).
    have htb:tr b=mu%:R.
      exact (@continuous_at_closure_closed_value (real_norm_metric_space hNX) Y tr
        (B `&` G) b [set (mu%:R:R^o)] hc hclosed hSval hcl).
    have [r [hr hrn]]:=linear_rank_exists (D b) (@coordinate_basisP R n).
    have he:r=mu.
      have hh:(r%:R:R)=mu%:R:=eq_trans (esym (@htrank b hb r hr)) htb.
      by move: hh=>/eqP; rewrite eqr_nat=>/eqP.
    split=>//; apply: (hExact b hbA).2; by rewrite -he.
have hAll:(B `&` G)=B.
  apply: (hB (B `&` G) hSG).
  - by exists G.
  - exists ClS; [exact: closed_closure|exact hClosedRep].
exists mu; split=>// b hb.
have hbG:G b by have hh:=hb; rewrite -hAll in hh; exact hh.2.
have hnb:=hGo; rewrite openE in hnb.
have hInt:=proj2 (@norm_domain_interior_neighbourhood R X NX hNX G b)
  (hnb b hbG).
have [d [hd hball]]:=hInt.
exists d; split=>// v hv.
have hx:=hball v hv; split; first exact hx.1.
exact: (hExact _ hx.1).1 hx.2.
Qed.
