(** Federer (1969), 2.10.39, printed p. 199: multiplying the first m-1
    integer brackets and the m-th side gives the stated total diameter-power
    bound. This supporting consequence uses the abstract count laws and the
    equality between the mesh and that last side, without inspecting chosen
    counts. Source context: BoxSubdivisionCountsUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import BoxSubdivisionCountsUP BoxSubdivisionCountsLaws
  RectangularGridUP FinitePrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_box_mesh_budget]: supporting
    m-th diameter-power estimate in 2.10.39, p. 199,
    before multiplication by n^(m/2). Here m=p+1,
    and h is the m-th side of the ordered box. *)
Theorem positive_box_mesh_budget (R : realType) n p (hp : (p<n)%N)
    (c : 'I_n -> R) h count :
  is_box_subdivision_counts c p h count -> h=c (Ordinal hp) ->
  #|rectangular_grid_indices count|%:R*h^+p.+1<=
    2^+p*\prod_(i<p.+1) family_prefix hp c i.
Proof.
move=> hD hh.
pose hp0 := ltnW hp.
have hprod : (\prod_(i<p.+1) family_prefix hp c i)=
    (\prod_(i<p) family_prefix hp0 c i)*h.
  rewrite big_ord_recr; congr (_*_).
  - apply: eq_bigr=> i _; rewrite /family_prefix; congr (c _); exact: val_inj.
  - rewrite hh /family_prefix; congr (c _); exact: val_inj.
have hb := box_subdivision_mesh_product_bound hD hp0.
have hnonneg := ltW (box_subdivision_mesh_positive_law hD).
have hbound := ler_wpM2r hnonneg hb.
rewrite hprod exprSr !mulrA.
exact hbound.
Qed.
