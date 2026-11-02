(** Supporting finite-dimensional topology for Federer (1969),
    3.1.21, p. 234: vector subspaces of Euclidean space are
    closed. The argument expands the adapted-coordinate proof
    already used in 2.7.16, p. 138, for arbitrary supplied norms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier LinearBasis FiniteDualDimension
  SubspaceStabiliser RealNormUP NormMetric NormDifferentialUP NormFiniteLinearBound NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_subspace_closed]: supporting closedness
    of the finite-dimensional planes used in Federer 3.1.21,
    p. 234. Extend a subspace basis and express membership by
    the vanishing complementary continuous coordinates, as in
    the supporting proof for 2.7.16, p. 138. *)
Theorem finite_norm_subspace_closed (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) n (b:'I_n->X) (hb:is_basis b)
    (W:subspace X) m (hW:exists w:'I_m->subspace_space W,is_basis w) :
  @closed (real_norm_metric_space hN) (W:set X).
Proof.
have [w hw]:=hW.
have [e [heb hew]]:=adapted_basis_exists hb hw.
pose M:=real_norm_metric_space hN.
have heq:(W:set M)=
  \bigcap_(j in [set: 'I_(n-m)]) [set x:M|dual_basis heb (rshift m j) x=0].
  apply/seteqP; split=>x.
  - move=>hx j _; exact: ((adapted_subspaceE hw heb hew x).1 hx j).
  - move=>hx; apply/(adapted_subspaceE hw heb hew x)=>j; exact: hx j I.
rewrite heq; apply: closed_bigI=>j _.
pose L:=hom_of_linear (dual_basis heb (rshift m j)).
pose Y:=real_norm_metric_space (scalar_absolute_value_norm R).
have hc:continuous (fun x:M=>(L x:Y)).
  apply: norm_bounded_linear_continuous.
  exact (@norm_finite_linear_bounded R X R^o N (fun t:R^o=>`|t|) hN
    (scalar_absolute_value_norm R) n b hb L).
have h0:@closed Y [set 0].
  exact (@compact_closed Y _ (@metric_hausdorff R Y) (@compact_set1 Y 0)).
change (@closed M ((fun x:M=>(L x:Y)) @^-1` [set 0])).
apply: preimage_closed; last exact h0.
move=>x _; exact: hc x.
Qed.
