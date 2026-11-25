(** Federer (1969), 2.3.5, p. 76: existence of finitely many disjoint closed
    pieces. Source context: LusinPiecesUP.v. Closed approximation is an
    abstract premise, later discharged by 2.2.3 or 2.2.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureSplit
  MeasureAlmostUP MeasurableFunctionUP MeasurableFunctionBorel
  MeasureFiniteClosure TopologicalBorel ClosedApproximationUP
  SmallBorelPartitionUP SmallBorelPartitionSealed LusinPiecesUP
  MeasureFinitePrefixError SetSequenceDisjointification GeometricErrorBudget MeasureGeometricCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_finite_closed_pieces]: the finite approximation
    assertion in the proof of Federer 2.3.5, pp. 76–77 No target
    inhabitation or finite total-measure premise is introduced. *)
Theorem lusin_finite_closed_pieces (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (A : set X) (f : partial_function X Y) (eta delta : R) :
  countable D -> dense D ->
  (forall K, closed K -> measure_measurable mu K) ->
  (forall H, measure_measurable mu H -> mu H < +oo -> is_closed_approximable mu H) ->
  is_measure_measurable_function mu f -> measure_measurable mu A -> mu A < +oo ->
  (0 < eta)%R -> (0 < delta)%R ->
  exists N E, is_lusin_piece_system mu A f eta delta N E.
Proof.
move=> hc hd hclosed happ hf hA hfin heta hdelta.
pose B := @SmallBorelPartition.value R Y D eta hc hd heta.
have hB := @SmallBorelPartition.laws R Y D eta hc hd heta.
pose H n := A `&` partial_function_preimage f (B n).
have hmH n : measure_measurable mu (H n).
  apply: (@measure_measurable_intersection R X mu hm _ _ hA).
  exact: (@measurable_function_borel_preimage R X Y mu hm f hf _ (small_partition_borel hB n)).
have hfH n : mu (H n) < +oo.
  apply: le_lt_trans _ hfin; apply: (@measure_mono R X mu hm)=> x [hx _]; exact hx.
have hex n := happ (H n) (hmH n) (hfH n) _ (geometric_error_budget_positive n hdelta).
pose E n := projT1 (cid (hex n)).
have hE n : closed (E n) /\ E n `<=` H n /\
    mu (H n `\` E n) < (geometric_error_budget delta n)%:E.
  exact: projT2 (cid (hex n)).
pose F n := H n `\` E n.
have hbound : mu (\bigcup_n F n) < delta%:E.
  exact: (proj2 (@measure_geometric_cover_bound R X mu hm _ F delta hdelta
    (fun x hx => hx) (fun n => (hE n).2.2))).
have herror : mu (A `\` \bigcup_n E n) < delta%:E.
  have hcover : (A `\` \bigcup_n E n) `<=`
      (~` partial_function_domain f) `|` (\bigcup_n F n).
    move=> x [ha hn]; case: (pselect (partial_function_domain f x))=> hx; last by left.
    right; have [y hxy] := hx.
    have hy : (\bigcup_n B n) y by rewrite (small_partition_cover hB).
    have [n _ hby] := hy; exists n; first exact Logic.I; split.
    + split=> //; exists y; by split.
    + move=> he; apply: hn; by exists n.
  have hb := @measure_binary_cover R X mu hm _ _ _ hcover.
  have hnull : mu (~` partial_function_domain f) = 0 := measurable_function_domain hf.
  rewrite hnull add0e in hb; exact: le_lt_trans hb hbound.
have [N hN] := @measure_finite_prefix_error R X mu hm A E delta%:E hA hfin
  (fun n => hclosed _ (hE n).1) herror.
exists N, E; constructor.
- move=> n _; exact: (hE n).1.
- move=> n _ x hx; have [ha [y [hy hb]]] := (hE n).2.1 x hx.
  split=> //; by exists y.
- move=> n m _ _ hnm x hx hz.
  have [_ [y [hy hby]]] := (hE n).2.1 x hx.
  have [_ [w [hw hbw]]] := (hE m).2.1 x hz.
  have he := @partial_function_single_valued X Y f x y w hy hw.
  rewrite -he in hbw; exact (@small_partition_disjoint R Y eta B hB n m hnm y hby hbw).
- move=> n _ x z y w hx hz hxy hzw.
  have [_ [u [hu hbu]]] := (hE n).2.1 x hx.
  have [_ [v [hv hbv]]] := (hE n).2.1 z hz.
  have heu := @partial_function_single_valued X Y f x u y hu hxy.
  have hev := @partial_function_single_valued X Y f z v w hv hzw.
  rewrite heu in hbu; rewrite hev in hbv.
  exact: (@small_partition_diameter R Y eta B hB n y w hbu hbv).
- exact hN.
Qed.
