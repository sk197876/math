(** Federer (1969), 3.1.19(4), p. 231: actual
    coordinate patches of a compact submanifold admit a
    finite compact refinement. Supporting the reduction to
    sphere-contained class-one covering manifolds in 3.2.47,
    p. 283. Chart choices stay inside an existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp finmap classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric HilbertFormCompactness NormDifferentialUP NormRegularity
  NormClassZeroTopology NormCoordinateSystemUP InnerNormTopologyAdapters
  FiniteInnerSubmanifoldUP FiniteInnerSubmanifoldCoordinates CompactOpenCoverClosedCores MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CoordinateCores.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Variable d:nat.
Local Notation Z:=(R_n R d).
Local Notation J:=((set V)*(set Z*((V->Z)*(Z->V))))%type.
Local Notation X:=(inner_metric_space hB).
Variable S:set V.

(** Source for [finite_inner_compact_coordinate_cores]: a
    finite compact core cover subordinate to actual local
    coordinate patches of 3.1.19(4), p. 231,
    supporting 3.2.47, p. 283. Both coordinate
    maps, the parameter domain and exact original ambient
    source are retained, without a globally selected atlas. *)
Theorem finite_inner_compact_coordinate_cores:
  is_inner_submanifold B d 1%N S ->@compact X S ->
  exists F:{fset (J*(V*R))%type},
    (forall p,p \in F ->
      is_norm_coordinate_system (inner_norm_real_norm hB)
        (inner_norm_real_norm (@euclidean_inner_productP R d)) S
        p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 1%N /\
      @compact X (S `&` @metric_closed_ball R X p.2.1 p.2.2) /\
      (S `&` @metric_closed_ball R X p.2.1 p.2.2) `<=` p.1.1) /\
    S `<=` \bigcup_(p in [set` F]) (S `&` @metric_closed_ball R X p.2.1 p.2.2).
Proof.
move=>hS hCompact.
pose D:set J:=fun q=>is_norm_coordinate_system (inner_norm_real_norm hB)
  (inner_norm_real_norm (@euclidean_inner_productP R d)) S q.1 q.2.1 q.2.2.1 q.2.2.2 1%N.
pose U:=fun q:J=>q.1.
have hOpen q (hq:D q):@open X (U q).
  apply:(inner_norm_openP hB (U q)).2.
  exact (norm_class_zero_domain_open (norm_class_continuous (norm_coordinate_class_forward hq))).
have hCover:S `<=` \bigcup_(q in D) U q.
  move=>a ha.
  have [T [Q [phi [psi [hBase [_ hChart]]]]]]:=
    @finite_inner_submanifold_coordinates R V B hB d 1%N S a hS ha.
  exists (T,(Q,(phi,psi))); first exact hChart.
  exact (norm_domain_interior_member (inner_norm_real_norm hB) hBase).
have [F [hF hFCover]]:=@compact_open_cover_closed_cores R X [the choiceType of J]
  D U S hCompact hOpen hCover.
exists F; split; last exact hFCover.
move=>p hp; have [hChart [_ [hK hIn]]]:=hF p hp.
exact (conj hChart (conj hK hIn)).
Qed.
End CoordinateCores.
