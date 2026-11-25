(** Federer (1969), 3.3.19, p. 304:
    every original level piece has Hausdorff mass
    twice the original level radius. Exact original
    translations and finite disjoint additivity prove it. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls InnerTranslationNeighbourhood
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularDiscTreeUP CircularDiscTreeTopology
  CircularDiscTreeExactCount CircularDiscLimitUP CircularDiscLevelPieces CircularDiscPieceTranslations CircularDiscExactMass
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffIsometricEmbedding
  MeasureUP MeasureBasic MeasureFiniteAdditivity BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_piece_Hausdorff_mass_equal]:
    congruent original A-level pieces have equal
    actual H1 masses, supporting the exact values
    in 3.3.19, p. 304. Apply
    the actual translation isometry to the proved
    identity of original sets. *)
Lemma circular_disc_piece_Hausdorff_mass_equal j (c d:E):
  c \in H j ->d \in H j ->
  mu (A `&` metric_closed_ball c (rho j))= mu (A `&` metric_closed_ball d (rho j)).
Proof.
move=>hc hd.
have hImage:= @circular_disc_level_pieces_translates R H hH A hA j c d hc hd.
have hInverse:cancel (fun x:E=>x+(d-c)) (fun x:E=>x-(d-c)) by move=>x;by rewrite addrK.
have hMass:= @hausdorff_isometric_embedding_invariance R [the metricType R of E] [the metricType R of E]
  (fun x=>x+(d-c)) (fun x=>x-(d-c)) hInverse
  (fun x y=>@inner_translation_distance R _ (@euclidean_inner_product R 2)
    (@euclidean_inner_productP R 2) (d-c) x y) 1 (A `&` metric_closed_ball c (rho j)).
by rewrite hImage in hMass;symmetry.
Qed.

(** Source for [circular_disc_piece_Hausdorff_mass]:
    H1(A intersect B)= 2 rho_n for every
    actual B in G_n, exactly 3.3.19,
    p. 304. Actual finite closed pieces
    partition original A, their proved translated
    masses agree, and their exact factorial count
    times radius equals one. *)
Theorem circular_disc_piece_Hausdorff_mass j (c:E):c \in H j ->
  mu (A `&` metric_closed_ball c (rho j))=(2* rho j)%:E.
Proof.
move=>hc.
have hMu:= @hausdorff_measure_is_measure R [the metricType R of E] 1.
have hReg:= @hausdorff_measure_borel_regular R [the metricType R of E] 1.
have [hNonempty hCompact]:= @circular_disc_limit_nonempty_compact R H hH A hA.
have hAClosed:closed A:= compact_closed (@metric_hausdorff R [the metricType R of E]) hCompact.
pose P:= fun z:E=>A `&` metric_closed_ball z (rho j).
have hMeas z:z \in H j ->measure_measurable mu (P z).
  move=>hz;apply:(@borel_regular_borel_measurable R [the topologicalType of E] mu hMu hReg).
  apply:closed_borel_set;apply:closedI;first exact hAClosed.
  exact:metric_closed_ball_closed.
have hDisjoint z w:z \in H j ->w \in H j ->z!=w ->forall x,P z x ->P w x ->False.
  move=>hz hw hDifferent x [_ hxZ] [_ hxW].
  have hEqual:= @circular_disc_level_point_unique R H hH j x z w hz hw hxZ hxW.
  by move:hDifferent;rewrite hEqual eqxx.
have hPartition:= @measure_finite_disjoint_additivity R E E mu hMu P (H j) hMeas hDisjoint.
have hUnion:(\bigcup_(z in [set` H j]) P z)= A.
  apply/seteqP;split.
  - by move=>x [z hz [hxA _]].
  - move=>x hxA;have [z [hz hxZ]]:=(hA x).1 hxA j.
    exists z=>//;by split.
rewrite hUnion (@circular_disc_hausdorff_mass R H hH A hA) in hPartition.
have hBound:(mu (P c)< +oo)%E.
  apply:(le_lt_trans (@measure_mono R E mu hMu (P c) A (fun x hx=>hx.1))).
  by rewrite (@circular_disc_hausdorff_mass R H hH A hA) ltry.
have hFinite:mu (P c) \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hMu (P c))).
pose m:R:= fine (mu (P c)).
have hValue:mu (P c)= m%:E by rewrite /m fineK.
have hEach z:z \in H j ->mu (P z)= m%:E.
  move=>hz;rewrite -hValue;exact:(@circular_disc_piece_Hausdorff_mass_equal j z c hz hc).
have hSum:(\sum_(z<-H j) mu (P z))=((N j)%:R* m)%:E.
  transitivity (\sum_(z<-H j) m%:E).
  - apply:eq_big_seq=>z hz;exact:hEach z hz.
  - by rewrite sumEFin big_seq_fsetE sumr_const cardT -cardE -cardfE
      (@circular_disc_tree_exact_count R H hH j) mulr_natl.
have hCountMass:2=(N j)%:R* m by exact:EFin_inj (eq_trans hPartition hSum).
have hBudget:= @factorial_disc_count_radius R N rho (@FactorialDiscScales.laws R) j.
have hScaled:= congr1 (fun x:R=>x* rho j) hCountMass.
have hCancel:((N j)%:R* m)* rho j= m.
  by rewrite [((N j)%:R* m)]mulrC -mulrA hBudget mulr1.
rewrite hCancel in hScaled.
by rewrite -/P hValue -hScaled.
Qed.
End Mass.
