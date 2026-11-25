(** Federer (1969), 4.1.18, p. 377:
    Closure is taken in the original
    L1 pair seminorm J. The existing
    opaque directed-seminorm topology applies to
    this one-member family without identifying
    null raw fields or imposing separation. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentLonePairImageUP CurrentLonePairCost OpenFamilyTopologyUP
  OpenFamilyTopologyMathcomp DirectedSeminormFamilyUP
  DirectedSeminormTopologySealed DirectedSeminormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PairTopology.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation hJ := (@current_lone_pair_cost_seminorm R h2 n m U hU).

(** Source for [current_lone_pair_cost_directed_family]:
    the single original pair seminorm J
    supplies the topology in the kernel
    closure of Federer 4.1.18, p. 377.
    Its null vectors need not be zero. *)
Theorem current_lone_pair_cost_directed_family :
  is_directed_seminorm_family (fun _ : unit => J).
Proof.
constructor.
- by exists tt.
- by move=> i; exact: hJ.
- move=> i j; exists tt=> v; by split.
Qed.

(** Source for [current_lone_pair_opens]: the
    original J topology on Omega_m times
    Omega_(m+1), used by Closure in Federer
    4.1.18, p. 377. Reuse the
    independently specified opaque seminorm topology. *)
Definition current_lone_pair_opens : set (set P) :=
  @DirectedSeminormTopology.opens R P unit (fun _ => J)
    current_lone_pair_cost_directed_family.

(** Source for [current_lone_pair_topology_laws]:
    the actual J topology has exactly
    the positive-radius translated J-ball neighbourhoods,
    supporting Closure in Federer 4.1.18,
    p. 377. No Hausdorff assertion
    is made for the raw pair fields. *)
Theorem current_lone_pair_topology_laws :
  is_seminorm_family_topology (fun _ : unit => J) current_lone_pair_opens.
Proof. exact: DirectedSeminormTopology.laws. Qed.

(** Source for [current_lone_pair_closure_balls]:
    Closure in the original J topology
    is exactly approximation to every positive
    J error, supporting the displayed kernel
    identity in Federer 4.1.18, p. 377.
    The old neighbourhood specification supplies both directions. *)
Theorem current_lone_pair_closure_balls (G : set P) (v : P) :
  @closure (open_family_topological_space current_lone_pair_topology_laws.1) G v <->
  forall epsilon : R, 0 < epsilon -> exists w : P, G w /\ J (v-w)%R < epsilon.
Proof.
split.
- move=> hClosure epsilon hEpsilon.
  have hOpen := @seminorm_family_ball_open R P unit (fun _ => J)
    current_lone_pair_opens current_lone_pair_cost_directed_family
    current_lone_pair_topology_laws tt v epsilon.
  have hPoint : J (v-v)%R < epsilon.
    by rewrite subrr (real_seminorm_zero hJ).
  pose Top := [the topologicalType of
    (open_family_topological_space current_lone_pair_topology_laws.1)].
  have hNear : @nbhs Top Top v [set w | J (w-v)%R < epsilon].
    exact: (@open_nbhs_nbhs Top v [set w | J (w-v)%R < epsilon]
      (conj hOpen hPoint)).
  have [w [hW hDistance]] := hClosure _ hNear.
  exists w; split; first exact: hW.
  by rewrite (real_seminorm_subtract hJ).
- move=> hApprox A hA.
  rewrite nbhsE in hA.
  have [B [hB hVB] hBA] := hA.
  have [i [epsilon [hEpsilon hBall]]] :=
    (current_lone_pair_topology_laws.2 B).1 hB v hVB.
  have [w [hW hDistance]] := hApprox epsilon hEpsilon.
  exists w; split; first exact: hW.
  apply: hBA; apply: hBall.
  by rewrite (real_seminorm_subtract hJ).
Qed.
End PairTopology.
