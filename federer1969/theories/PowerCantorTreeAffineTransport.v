(** Federer (1969), 3.3.20, pp. 307–308:
    positive similarities preserve every original recursive interval level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  AffineIntervalTransportUP AffineIntervalTransportInverse PowerCantorFamilyAffineTransport
  SpecialIntervalRefinement RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [power_cantor_tree_positive_affine_transport]:
    supporting ACTUAL original-level similarities in
    3.3.20, pp. 307–308. The image
    of each original level satisfies the original
    equal-cost recursion at the transformed root,
    with exactly the original subdivision schedule.
    Every transformed child law is proved from
    the original Phi laws. The auxiliary inverse
    and child selectors remain local. *)
Theorem power_cantor_tree_positive_affine_transport (R:realType) (a r c m:R)
    M (J:compact_real_intervals R) n H:
  0<r ->is_affine_interval_transport a r M ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) (M J) n
    (fun j=>[fset M S|S in H j]).
Proof.
move=>hr hM hTree.
have [N [hN [hMN hNM]]]:=affine_interval_transport_inverse_exists hr hM.
constructor.
- by rewrite (equal_cost_tree_root hTree) imfset_fset1.
- move=>j.
  have [K [hK hNext]]:=equal_cost_tree_step hTree j.
  pose L U:=[fset M S|S in K (N U)].
  exists L;split.
  + move=>U /imfsetP[P hP hU].
    rewrite hU /L hMN.
    exact:(@power_cantor_family_positive_affine_transport R a r c m M P (n j) (K P)
      hr hM (hK P hP)).
  + rewrite hNext;apply/fsetP=>U;apply/idP/idP.
    * move=>/imfsetP[V /special_interval_refinement_membership[P [hP hV]] hU].
      apply/special_interval_refinement_membership;exists (M P);split.
      -- apply/imfsetP;by exists P.
      -- rewrite /L hMN;apply/imfsetP;by exists V.
    * move=>/special_interval_refinement_membership[T [/imfsetP[P hP hT] hU]].
      rewrite hT /L hMN in hU.
      move:hU=>/imfsetP[V hV hU].
      apply/imfsetP;exists V=>//.
      apply/special_interval_refinement_membership;by exists P.
Qed.
