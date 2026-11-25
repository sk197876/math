(** Federer (1969), 3.1.13, p. 225:
    a locally finite family of containing supports
    gives a locally finite family of functions. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology LocallyFiniteFamilyUP NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_locally_finite_supported_family]:
    the locally finite refinement in Federer
    3.1.13, p. 225, makes
    the bump-function sum locally finite.
    Closedness of the containing sets is not
    needed for this supporting implication. *)
Theorem norm_locally_finite_supported_family (R : realType)
    (X : lmodType R) (Y : zmodType) (J : choiceType)
    (NX : X->R) (hNX : is_real_norm NX)
    (U : set X) (I : set J) (F : J->set X) (f : J->X->Y) :
  (forall x, U x -> norm_domain_interior NX U x) ->
  @is_locally_finite_family_on [the topologicalType of real_norm_metric_space hNX]
    J U I F ->
  (forall j, I j -> forall x, f j x<>0 -> F j x) ->
  is_norm_locally_finite_function_family NX U I f.
Proof.
move=>hU hlocal hsupp a ha.
have [V [hVo [hVa hfinite]]] := hlocal a ha.
pose O := V `&` U.
have hUo : @open [the topologicalType of real_norm_metric_space hNX] U.
  rewrite openE=>x hx; exact: ((norm_domain_interior_neighbourhood hNX U x).1 (hU x hx)).
have hOo : @open [the topologicalType of real_norm_metric_space hNX] O.
  exact: (openI hVo hUo).
pose K := I `&` [set j | exists x, V x /\ F j x].
pose E := fset_set K.
have hEI j : j \in E -> I j.
  rewrite /E in_fset_set //; move/set_mem=>[hj _]; exact hj.
exists O; split; first exact: (conj hVa ha).
split; first by move=>x [_ hx].
split.
- move=>x hx; apply: (norm_domain_interior_neighbourhood hNX O x).2.
  by move: hOo; rewrite openE; apply.
- exists E; split; first exact hEI.
  move=>x [hVx hUx] j hj hnot.
  case: (eqVneq (f j x) 0)=>[he|hne]; first exact he.
  have hin : j \in E.
    rewrite /E in_fset_set //; apply/mem_set; split; first exact hj.
    exists x; split; first exact hVx.
    apply: (hsupp j hj x)=>he; by move: hne; rewrite he eqxx.
  by move: hnot; rewrite hin.
Qed.
