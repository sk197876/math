(** Federer (1969), 3.4.10, p. 337:
    pass from local finite outer mass to finite
    mass on every compact subset of the original
    domain. Reuse compact finite covers and the
    existing finite indexed outer-measure bound. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import CompactFiniteCover MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_local_finite_mass]: the compact
    assembly in 3.4.10, p. 337, without
    measurability of the original set or of the
    local pieces. Only finite outer mass is used. *)
Theorem compact_local_finite_mass (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (S K:set X):
  is_measure mu ->compact K ->
  (forall a,K a ->exists O:set X,open O /\O a /\mu (S `&` O)< +oo) ->
  mu (S `&` K)< +oo.
Proof.
move=>hMu hK hLocal.
pose D:set (set X):=[set O|open O /\mu (S `&` O)< +oo].
have hCover:K `<=` \bigcup_(O in D) O.
  move=>a ha;have [O [hOpen [haO hFinite]]]:=hLocal a ha.
  exists O;[by split|exact:haO].
have [F hFD hFCover]:=@compact_open_finite_cover X [the choiceType of set X]
  D (fun O=>O) K hK (fun O hO=>hO.1) hCover.
have hSubset:S `&` K `<=` \bigcup_(i:F) (S `&` val i).
  move=>a [haS haK];have [O hOF haO]:=hFCover a haK.
  exists ([` hOF]%fset);first exact:Logic.I.
  by split.
have hMass (i:F):mu (S `&` val i)< +oo.
  exact:(set_mem (hFD (val i) (valP i))).2.
have hValue (i:F):mu (S `&` val i)=(fine (mu (S `&` val i)))%:E.
  have hFinite:mu (S `&` val i) \is a fin_num.
    rewrite ge0_fin_numE;first exact:hMass i.
    exact:measure_nonnegative hMu _.
  by rewrite fineK.
have hSumEquation:(\sum_(i:F) mu (S `&` val i))=(\sum_(i:F) fine (mu (S `&` val i)))%:E.
  rewrite -sumEFin;apply:eq_bigr=>i _;exact:hValue i.
have hSum:(\sum_(i:F) mu (S `&` val i))< +oo by rewrite hSumEquation ltry.
exact:(le_lt_trans (@measure_finite_indexed_cover R X (F:finType) mu hMu
  (S `&` K) (fun i:F=>S `&` val i) hSubset) hSum).
Qed.
