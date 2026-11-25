(** The geometric-level partition in Federer (1969), 2.9.7, p. 156:
    t^j<=f<t^(j+1), j an integer and t>1. The partition is specified
    directly by inverse images, while coverage and uniqueness reuse the
    proved geometric cells of 2.4.4(2), p. 83. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasurableFunctionUP
  MeasurableFunctionBorel CountableOrderIntervals TopologicalBorel BorelFamilyBasic
  MeasureUP GeometricIntegerCells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [geometric_function_band]: direct geometric
    level used for P^n in Federer 2.9.7,
    p. 156, before intersection with the target A.
    The graph enforces f's original partial domain. *)
Definition geometric_function_band (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) (t : R) (j : int) :=
  partial_function_preimage f [set y | (t^j)%:E<=y /\ y<(t^(j+1))%:E].

(** Source for [geometric_function_band_measurable]: the
    measurability of P^n attributed to 2.9.6 in
    Federer 2.9.7, p. 156. A half-open
    band is the intersection of a closed upper
    ray and an open lower ray in the extended line. *)
Lemma geometric_function_band_measurable (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) t j :
  is_measure phi -> is_measure_measurable_function phi f ->
  measure_measurable phi (geometric_function_band f t j).
Proof.
move=> hm hf; apply: (@measurable_function_borel_preimage R X (extended_real_line R) phi hm f hf).
apply: (@borel_family_binary_intersection (extended_real_line R) setT _ (borel_sets_family (extended_real_line R))).
- apply: closed_borel_set.
  exact (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] (t^j)%:E).
- apply: open_borel_set.
  exact (@order_strict_lower_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] (t^(j+1))%:E).
Qed.

(** Source for [geometric_function_band_disjoint]: the
    disjointness of the integer level sets in Federer
    2.9.7, p. 156. Single-valuedness identifies
    the common value, and geometric cell uniqueness
    applies after its finiteness is proved. *)
Lemma geometric_function_band_disjoint (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) (t : R) i j x :
  (1<t)%R -> geometric_function_band f t i x -> geometric_function_band f t j x -> i=j.
Proof.
move=> ht [y [hy [hil hiu]]] [z [hz [hjl hju]]].
have he := partial_function_single_valued hy hz; rewrite -he in hjl hju.
have ht0 : (0<t)%R := lt_trans (@ltr01 R) ht.
have hip : (0<t^i)%R by rewrite exprz_gt0.
have hi0 : 0<=(t^i)%:E by rewrite lee_fin; exact: ltW hip.
have hy0 : 0<=y := le_trans hi0 hil.
have hyf : y< +oo := lt_trans hiu (ltry _).
have hyfin : y \is a fin_num by rewrite (ge0_fin_numE hy0).
rewrite -(fineK hyfin) !lee_fin in hil hjl.
rewrite -(fineK hyfin) !lte_fin in hiu hju.
exact: geometric_integer_cell_unique ht hil hiu hjl hju.
Qed.

(** Source for [geometric_function_bands_cover]: the
    exhaustion of positive finite values in Federer 2.9.7,
    p. 156, after removal of zero and
    non-real values. This equality includes the partial
    domain qualification explicitly. *)
Lemma geometric_function_bands_cover (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) (t : R) :
  (1<t)%R -> (\bigcup_j geometric_function_band f t j)=
    [set x | exists y, partial_function_graph f x y /\ 0<y /\ y< +oo].
Proof.
move=> ht; have ht0 : (0<t)%R := lt_trans (@ltr01 R) ht.
apply/seteqP; split.
- move=> x [j _ [y [hy [hlo hhi]]]]; exists y; split=> //; split.
  + apply: lt_le_trans _ hlo; rewrite lte_fin; by rewrite exprz_gt0.
  + exact: lt_trans hhi (ltry _).
- move=> x [y [hy [hy0 hyf]]].
  have hyfin : y \is a fin_num by rewrite (ge0_fin_numE (ltW hy0)).
  have hr0 : (0<fine y)%R by move: hy0; rewrite -(fineK hyfin) lte_fin.
  have [j [hlo hhi]] := @geometric_integer_cell_exists R t (fine y) ht hr0.
  exists j; first exact I.
  exists y; split; first exact hy.
  split.
  - by rewrite -(fineK hyfin) lee_fin.
  - by rewrite -(fineK hyfin) lte_fin.
Qed.
