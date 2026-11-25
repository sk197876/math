(** Federer (1969), 4.1.1, pp. 344–346: real scalar
    multiplication is continuous for weak dual topologies. This
    supports the sign in distributional differentiation without
    assuming vector continuity for the final test-function topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormOpenTopology OpenFamilyTopologyUP
  OpenFamilyContinuousOperations DirectedSeminormVectorTopology WeakEvaluationTopologyUP
  WeakEvaluationTopologyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weak_linear_evaluation_scaling_continuous]:
    multiplication by a fixed real scalar is weakly continuous,
    supporting D_j T=-TD_j and D^alpha T=(-1)^i TD^alpha in
    Federer 4.1.1, p. 346. Only the actual linear evaluation
    and the independent weak topology laws are used. *)
Theorem weak_linear_evaluation_scaling_continuous (R:realType)
    (E D:lmodType R) (ev:Hom D (Hom E R^o)) (O:set (set D)):
  is_weak_evaluation_topology (fun T x=>ev T x) O -> forall c:R,
    open_family_continuous O O (fun T=>c*:T).
Proof.
move=>hO c; apply:(hO.2 D O hO.1 (fun T=>c*:T)).2=>x.
have hEval:=weak_evaluation_continuous hO x.
pose hN:=@scalar_absolute_value_norm R.
have hR:=seminorm_family_vector_topology (norm_single_seminorm_directed hN)
  (norm_open_family_seminorm_laws hN).
have hScale:=@open_family_continuous_scale R D R^o O (norm_open_family hN)
  hO.1 hR (fun T=>ev T x) c hEval.
have he:(fun T:D=>ev (c*:T) x)=(fun T=>c*:ev T x).
  by apply:funext=>T; rewrite linearZ.
by rewrite he.
Qed.
