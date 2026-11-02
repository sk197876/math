(** Federer (1969), 3.1.24, p. 240, referring to 3.1.19, p. 231: the target chart of 3.1.18
    straightens a relatively open parametrised piece of B. This
    separates the set-theoretic shrinking from the rank theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness LinearRankUP LinearInjectiveRank
  NormDifferentialUP NormRegularity NormDiffeomorphismUP NormDiffeomorphismSourceRestriction
  NormMetric NormClassZeroTopology NormBoundedLinearTopology NormLinearDomainLaws EuclideanSubmanifoldUP AnalyticSubmanifoldUP NormAnalyticUP NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_diffeomorphism_plane_section]: 3.1.24, p. 240: supporting (3)
    implies (1), Federer 3.1.19, p. 231. If a diffeomorphism flattens
    a relatively open piece of B onto j(V), restricting its source
    gives exactly a vector-plane section of its image. *)
Theorem analytic_diffeomorphism_plane_section (R:realType) n mu
    (B S:set (R_n R n)) (V:set (R_n R mu))
    (p:{linear R_n R n->R_n R mu}) (j:{linear R_n R mu->R_n R n})
    (h H:R_n R n->R_n R n) b :
  cancel j p ->
  is_norm_diffeomorphism (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (fun x=>V (p x)) (fun x=>V (p x)) h H 1%N ->
  @norm_analytic R (R_n R n) (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun x=>V (p x)) h ->
  @norm_analytic R (R_n R n) (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun x=>V (p x)) H ->
  S `<=` [set x|V (p x)] -> h @` S=j @` V ->
  @relatively_open_set [the topologicalType of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] B S -> S b ->
  exists T C sigma tau Z, @is_analytic_submanifold_straightening R n mu B b T C sigma tau Z.
Proof.
move=>hjp hD hhA hHA hSM him [N [hN hSN]] hbS.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose M:=fun x:X=>V (p x).
pose T:=fun x:X=>M x /\ N x.
have hopenT x (hx:T x):norm_domain_interior NX T x.
  apply: norm_domain_intersection_interior.
  - have hc:=@norm_class_continuous R X X NX NX hNX hNX M h 1%N
      (norm_diffeomorphism_forward_class hD).
    exact (@hc x hx.1).1.
  - exact (proj2 (@norm_domain_interior_neighbourhood R X NX hNX N x)
      (open_nbhs_nbhs (conj hN hx.2))).
have hTM:T `<=` M by move=>x hx; exact hx.1.
have hDT:=@norm_diffeomorphism_source_restriction R X X NX NX hNX hNX
  M T M h H 1%N hD hTM hopenT.
pose C:=fun y:X=>M y /\ T (H y).
have hjinj:injective j:=can_inj hjp.
have hr:=@linear_injective_rank R (R_n R mu) X mu (@coordinate_basis R mu)
  (@coordinate_basisP R mu) n (@coordinate_basis R n) (@coordinate_basisP R n) (hom_of_linear j) hjinj.
pose Z:=@GrassmannSubspace R X mu (range_subspace (hom_as_linear (hom_of_linear j))) hr.
have hbN:N b by have hh:=hbS; rewrite hSN in hh; exact hh.2.
have hbT:T b:=conj (hSM b hbS) hbN.
have hhh:=@norm_analytic_open_restriction R X X NX NX hNX hNX M T h hTM hopenT hhA.
have hCopen x (hx:C x):norm_domain_interior NX C x.
  have hc:=norm_class_continuous (norm_diffeomorphism_inverse_class hDT).
  exact (@hc x hx).1.
have hHH:=@norm_analytic_open_restriction R X X NX NX hNX hNX M C H
  (fun x hx=>hx.1) hCopen hHA.
exists T,C,h,H,Z; split; last by split.
constructor; [exact: hopenT hbT|exact hDT|].
apply/seteqP; split=>y.
- move=>[x [hBx hTx] hxy].
  split.
  + have hxS:S x by rewrite hSN; split=>//; exact hTx.2.
    have hi:(h @` S) (h x) by exists x.
    rewrite him in hi; have [u hu hju]:=hi.
    exists u; exact (eq_trans (esym hxy) (esym hju)).
  + rewrite -hxy.
    exact (@norm_diffeomorphism_maps R X X NX NX hNX hNX T C h H 1%N hDT x hTx).
- move=>[hyZ hyC].
  have [u hju]:=hyZ.
  change (y=j u) in hju.
  have hu:V u.
    have hh:V (p y):=hyC.1.
    by rewrite hju hjp in hh.
  have hyj:(j @` V) y by exists u=>//; exact: esym hju.
  rewrite -him in hyj; have [x hxS hxy]:=hyj.
  have hxM:=hSM x hxS.
  have hHx:H y=x.
    rewrite -hxy; exact (@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX M M h H 1%N hD x hxM).
  exists (H y).
  + split; last exact hyC.2.
    have hxB:B x by rewrite hSN in hxS; exact hxS.1.
    by rewrite hHx.
  + exact (@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX M M h H 1%N hD y hyC.1).
Qed.
