(** Federer (1969), 3.2.14, pp. 251–252:
    replace a countable family of rectifiable sets
    by their closures and take finite initial unions.
    This supports finite-mass approximation without
    assuming the original parametrized images Borel. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RectifiableSetUP RectifiableElementary
  RectifiableClosure RectifiableUnion CountableDefaultEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_closed_increasing_cover]:
    closed rectifiable finite unions supporting the
    approximation assertion of Federer 3.2.14, p. 252.
    The union contains E and need not equal E. *)
Theorem rectifiable_closed_increasing_cover (R : realType)
    (X : metricType R) m (E : set X) :
  is_countably_m_rectifiable m E ->
  exists F : nat -> set X,
    (forall n, closed (F n) /\ is_m_rectifiable m (F n)) /\
    (forall n k, (n<=k)%N -> F n `<=` F k) /\
    E `<=` \bigcup_n F n.
Proof.
move=> [C [hc [hC hr]]].
have [u [hu hsur]] := countable_default_enumeration set0 hc.
pose G n := closure (u n).
have hG n : closed (G n) /\ is_m_rectifiable m (G n).
  split; first exact: closed_closure.
  apply: rectifiable_closure.
  have [hn|->] := hu n; first exact: hC (u n) hn.
  exact: rectifiable_empty.
pose F n := \bigcup_(i in [set i | (i<n)%N]) G i.
have hF0 : F 0%N=set0.
  apply/seteqP; split=> x; first by move=> [i hi _]; move: hi; rewrite /= ltn0.
  by move=> [].
have hFS n : F n.+1=F n `|` G n.
  apply/seteqP; split=> x.
  - move=> [i hi hx]; move: hi; rewrite /= ltnS leq_eqVlt=> /orP [/eqP he|hi].
    + right; by rewrite -he.
    + left; by exists i.
  - move=> [[i hi hx]|hx].
    + exists i=> //; exact: ltn_trans hi (ltnSn n).
    + exists n=> //; exact: ltnSn.
have hF n : closed (F n) /\ is_m_rectifiable m (F n).
  elim: n=> [|n [hcl hrn]].
  - rewrite hF0; split; [exact: closed0|exact: rectifiable_empty].
  - rewrite hFS; split; [exact: closedU hcl (hG n).1|exact: rectifiable_union hrn (hG n).2].
exists F; split=> //; split.
- move=> n k hnk x [i hi hx]; exists i=> //; exact: leq_trans hi hnk.
- move=> x hx; rewrite hr in hx; have [H hH hHx] := hx.
  have [n hn] := hsur H hH; exists n.+1=> //; exists n; first exact: ltnSn.
  rewrite /G hn; exact: subset_closure hHx.
Qed.
