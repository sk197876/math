(** Federer (1969), 2.10.39, printed p. 199: the number of small boxes times
    the m-th mesh power is bounded by 2^(m-1) times the first m side
    product. Derive the counting and cell-width estimates from the abstract
    integer brackets before selecting counts. Source context:
    BoxSubdivisionCountsUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import BoxSubdivisionCountsUP RectangularGridUP
  RectangularGridCardinality FinitePrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Counts.
Variable R : realType.
Variable n p : nat.
Variable c : 'I_n -> R.
Variable h : R.
Variable count : 'I_n -> nat.
Hypothesis hD : is_box_subdivision_counts c p h count.

(** Source for [box_subdivision_cell_width_bound]: supporting
    maximal side bound of each subdivided box in
    2.10.39, p. 199. The final unsplit sides
    must already have length at most the mesh. *)
Lemma box_subdivision_cell_width_bound :
  (forall i : 'I_n, (p<=i)%N -> c i<=h) -> forall i, c i/(count i)%:R<=h.
Proof.
move=> hc i; case: (ltnP i p)=> hi.
- have hk : 0<(count i)%:R :> R.
    rewrite ltr0n; exact (@box_subdivision_count_positive_law R n c p h count hD i).
  rewrite ler_pdivrMr // [h*(count i)%:R]mulrC.
  exact: (@box_subdivision_count_bracket_law R n c p h count hD i hi).1.
- rewrite (@box_subdivision_unsplit_law R n c p h count hD i hi) divr1.
  exact: hc.
Qed.

(** Source for [box_subdivision_grid_cardinality]: direct
    count k_1 ... k_(m-1) of the small boxes
    in 2.10.39, p. 199, with p=m-1.
    Unsplit final coordinates contribute the factor one. *)
Lemma box_subdivision_grid_cardinality (hp : (p<=n)%N) :
  #|rectangular_grid_indices count|=(\prod_(i<p) family_prefix hp count i)%N.
Proof.
rewrite rectangular_grid_cardinality (bigID (fun i : 'I_n=>(i<p)%N)) /=.
have ht : (\prod_(i<n | ~~(i<p)%N) count i= 1)%N.
  apply: big1=> i hi.
  apply: (@box_subdivision_unsplit_law R n c p h count hD i).
  by rewrite leqNgt.
by rewrite ht muln1 (big_ord_narrow hp).
Qed.

(** Source for [box_subdivision_mesh_product_bound]: supporting
    product estimate in 2.10.39, p. 199.
    Multiply the per-axis count brackets over the first
    p axes; zero split axes give the empty product one. *)
Theorem box_subdivision_mesh_product_bound (hp : (p<=n)%N) :
  #|rectangular_grid_indices count|%:R*h^+p<=
    2^+p*\prod_(i<p) family_prefix hp c i.
Proof.
rewrite (box_subdivision_grid_cardinality hp) natr_prod.
have hh : (\prod_(i<p) h)=h^+p by rewrite prodr_const card_ord.
have htwo : (\prod_(i<p) (2:R))= 2^+p by rewrite prodr_const card_ord.
rewrite -hh -htwo -!big_split.
apply: ler_prod=> i _; apply/andP; split.
- exact: mulr_ge0 (ler0n _ _) (ltW (box_subdivision_mesh_positive_law hD)).
- exact: (@box_subdivision_count_bracket_law R n c p h count hD
    (widen_ord hp i) (ltn_ord i)).2.
Qed.
End Counts.
