(** Federer (1969), 3.1.20, p. 233: the normal form for f(U)
    transfers to B on the common neighbourhood U. This supporting
    locality lemma uses exact image and inverse laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP NormRegularity NormClassZeroTopology
  NormBoundedLinearTopology NormLinearDomainLaws NormDiffeomorphismUP NormDiffeomorphismSourceRestriction
  EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_straightening_local_agreement]:
    supporting the final neighbourhood restriction of the converse
    proof of Federer 3.1.20, p. 233. If B and S agree on an
    open neighbourhood of b, a straightening of S restricts to
    a straightening of B. *)
Lemma submanifold_straightening_local_agreement (R:realType) n mu k
    (B S N T C:set (R_n R n)) b (sigma tau:R_n R n->R_n R n)
    (Z:G (R_n R n) mu) :
  @is_submanifold_straightening R n mu k S b T C sigma tau Z ->
  @open [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] N -> N b ->
  (forall x,N x -> (B x <-> S x)) ->
  exists T' C' sigma' tau' Z',@is_submanifold_straightening R n mu k B b T' C' sigma' tau' Z'.
Proof.
move=>[hTb hD him] hN hbN heq.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose U:=T `&` N.
have hopenU x (hx:U x):norm_domain_interior NX U x.
  have hc:=norm_class_continuous (norm_diffeomorphism_forward_class hD).
  exact (norm_domain_intersection_interior (@hc x hx.1).1
    (proj2 (@norm_domain_interior_neighbourhood R X NX hNX N x)
      (open_nbhs_nbhs (conj hN hx.2)))).
have hbT:T b:=norm_domain_interior_member hNX hTb.
have hbU:U b:=conj hbT hbN.
pose C':=fun y=>C y /\ U (tau y).
have hDU:=@norm_diffeomorphism_source_restriction R X X NX NX hNX hNX
  T U C sigma tau k hD (fun x hx=>hx.1) hopenU.
exists U,C',sigma,tau,Z; constructor; [exact: hopenU hbU|exact hDU|].
apply/seteqP; split=>y.
- move=>[x [hBx hUx] hxy]; split.
  + have hi:(sigma @` (S `&` T)) (sigma x).
      exists x; first exact: conj ((heq x hUx.2).1 hBx) hUx.1.
      reflexivity.
    rewrite him in hi; rewrite -hxy; exact hi.1.
  + rewrite -hxy; exact (@norm_diffeomorphism_maps R X X NX NX hNX hNX U C' sigma tau k hDU x hUx).
- move=>[hyZ hyC].
  have hi:(sigma @` (S `&` T)) y by rewrite him; exact: conj hyZ hyC.1.
  have [x [hSx hTx] hxy]:=hi.
  have ht:tau y=x.
    rewrite -hxy; exact (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C sigma tau k hD x hTx).
  exists (tau y); last exact (@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX T C sigma tau k hD y hyC.1).
  split; last exact hyC.2.
  apply: (heq _ hyC.2.2).2; by rewrite ht.
Qed.
