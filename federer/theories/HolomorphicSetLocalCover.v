(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.5, p. 321: the
    original germwise and open-cover definitions of a holomorphic
    subset agree. A finite holomorphic subvariety of an open
    domain is holomorphic throughout that domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP NormMetric SetGermUP SetGermExistence
  FiniteHolomorphicVarietyUP FiniteHolomorphicVarietyRestriction HolomorphicVarietyGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section LocalCover.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).

(** Source for [holomorphic_set_local_cover_equivalence]: the
    two equivalent definitions of S holomorphic in A in
    3.4.5, p. 321. The cover uses genuine
    open sets and the exact original intersections U intersect S. *)
Theorem holomorphic_set_local_cover_equivalence (A S:set X):
  is_holomorphic_set_in hNX A S <->has_local_holomorphic_variety_cover hNX A S.
Proof.
split.
- move=>hLocal a ha.
  have [U [V [haU [hVar hGerm]]]]:=hLocal a ha.
  have [W [hW [haW hEquality]]]:=(@set_germ_equality_original T a V S).1 hGerm.
  pose O:set X:=U `&` W.
  have hO:@open T O:=openI hVar.1 hW.
  exists O;split;first by split.
  have hRestriction:=@finite_holomorphic_variety_open_restriction R X NX hNX U O V hVar hO
    (fun x hx=>hx.1).
  have hSet:O `&` S=O `&` V.
    apply/seteqP;split.
    + move=>x [hx hs];split;first exact:hx.
      have hVW:(V `&` W) x by rewrite hEquality;split;[exact:hs|exact:hx.2].
      exact:hVW.1.
    + move=>x [hx hv];split;first exact:hx.
      have hSW:(S `&` W) x by rewrite -hEquality;split;[exact:hv|exact:hx.2].
      exact:hSW.1.
  by rewrite hSet.
- move=>hCover a ha;have [U [haU hVar]]:=hCover a ha.
  exists U,(U `&` S);split;first exact:haU.
  split;first exact:hVar.
  apply/(@set_germ_equality_original T a (U `&` S) S).
  exists U;split;first exact:hVar.1.
  split;first exact:haU.
  apply/seteqP;split.
  + by move=>x [[hu hs] hu'];split.
  + by move=>x [hs hu];split;first split.
Qed.

(** Source for [finite_holomorphic_variety_holomorphic_in_domain]:
    every holomorphic subvariety of an open A is holomorphic
    in A, 3.4.5, p. 321. *)
Lemma finite_holomorphic_variety_holomorphic_in_domain (A S:set X):
  is_finite_holomorphic_variety hNX A S ->is_holomorphic_set_in hNX A S.
Proof.
move=>hVar a ha;exists A,S;split;first exact:ha.
by split.
Qed.
End LocalCover.
