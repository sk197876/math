(** Federer (1969), 4.1.23, p. 379: an
    actual finite-image field supported in K is
    the finite sum of its constant-vector measurable
    cells. The same disjoint cells give its
    pointwise norm decomposition, preserving the exact
    mass budget rather than only a triangle bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp finmap
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages MeasureUP MeasureBasic MeasureFiniteClosure
  MeasurableFunctionUP MeasurableFunctionBorel MeasurableNormedFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FiniteCells.
Variable R : realType.
Variable X : choiceType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation VN := (real_norm_metric_space hN).

(** Source for [finite_image_measurable_cell_decomposition]: the
    third proof reduction of Federer 4.1.23,
    p. 379, yields genuine finite measurable
    cells inside the same K, with exact
    original point values and norm values. No
    nonzero-value or nonempty-domain assumption is needed. *)
Theorem finite_image_measurable_cell_decomposition
    (f : X -> VN) (K : set X) :
  is_measurable_normed_function mu (partial_function_total f) ->
  finite_set (f @` setT) -> measure_measurable mu K ->
  (mu K< +oo)%E -> (forall x, ~K x -> f x=0) ->
  exists (I : finType) (v : I -> V) (A : I -> set X),
    (forall i, measure_measurable mu (A i) /\ (mu (A i)< +oo)%E /\ A i `<=` K) /\
    (forall i j, i!=j -> forall x, A i x -> A j x -> False) /\
    (forall x, K x <-> exists i, A i x) /\
    (forall x, f x=\sum_i @CharacteristicFunction.value R X (A i) x*:v i) /\
    forall x, N (f x)=\sum_i @CharacteristicFunction.value R X (A i) x*N (v i).
Proof.
move=> hMeas hFinite hKMeas hKFinite hOff.
have [F hF] := finite_fsetP.1 hFinite.
pose I : finType := [the finType of (F:Type)].
pose v := fun i : I => (val i:V).
pose A := fun i : I => [set x | K x /\ f x=v i].
pose chi := fun i : I => @CharacteristicFunction.value R X (A i).
pose hChi := fun i : I => @CharacteristicFunction.laws R X (A i).
have hChiOn i x (hx : A i x) : chi i x= 1 := characteristic_on_set (hChi i) hx.
have hChiOff i x (hx : ~A i x) : chi i x=0 := characteristic_off_set (hChi i) hx.
have hCell i : measure_measurable mu (A i) /\ (mu (A i)< +oo)%E /\ A i `<=` K.
  have hSingleton : @borel_set VN [set (v i:VN)].
    apply: closed_borel_set; apply: accessible_closed_set1.
    apply: hausdorff_accessible; exact: (@metric_hausdorff R VN).
  have hPre := @measurable_function_borel_preimage R X VN mu hm
    (partial_function_total f) hMeas.1 [set (v i:VN)] hSingleton.
  have hSet : partial_function_preimage (partial_function_total f) [set (v i:VN)]=
      [set x | f x=v i].
    apply/seteqP; split.
    - move=> x [y [hValue hEqual]].
      have hY : f x=y := hValue; exact: eq_trans hY hEqual.
    - move=> x hx; exists (f x); by split.
  rewrite hSet in hPre.
  have hAK : A i `<=` K by move=> x hx; exact: hx.1.
  split; first exact: (@measure_measurable_intersection R X mu hm
    K [set x | f x=v i] hKMeas hPre).
  split; last exact: hAK.
  exact: le_lt_trans (measure_mono hm hAK) hKFinite.
have hDisjoint i j (hDifferent : i!=j) x (hAi : A i x) (hAj : A j x) : False.
  have hValues : v i=v j := eq_trans (esym hAi.2) hAj.2.
  have hSame : i=j := val_inj hValues.
  by move: hDifferent; rewrite hSame eqxx.
have hCover (x : X) : K x <-> exists i : I, A i x.
  split; last by move=> [i hx]; exact: hx.1.
  move=> hx.
  have hImage : (f @` setT) (f x) by exists x.
  have hMember : f x \in F by change ([set` F] (f x)); rewrite -hF.
  pose i : I := Sub (f x) hMember.
  exists i; by split.
have hOnCell i x (hx : A i x) :
    (\sum_j chi j x*:v j)=v i /\ (\sum_j chi j x*N (v j))=N (v i).
  have hOther j (hDifferent : j!=i) : ~A j x.
    move=> hAj; exact: (@hDisjoint j i hDifferent x hAj hx).
  split.
  - rewrite (bigD1 i) //= (@hChiOn i x hx) scale1r.
    have hZero : (\sum_(j|j!=i) chi j x*:v j)=0.
      apply: big1=> j hji.
      by rewrite (@hChiOff j x (@hOther j hji)) scale0r.
    by rewrite hZero addr0.
  - rewrite (bigD1 i) //= (@hChiOn i x hx) mul1r.
    have hZero : (\sum_(j|j!=i) chi j x*N (v j))=0.
      apply: big1=> j hji.
      by rewrite (@hChiOff j x (@hOther j hji)) mul0r.
    by rewrite hZero addr0.
exists I,v,A; split; first exact: hCell.
split; first exact: hDisjoint.
split; first exact: hCover.
split.
- move=> x; case: (pselect (K x))=> hx.
  + have [i hAi] := (@hCover x).1 hx.
    exact: eq_trans hAi.2 (esym (@hOnCell i x hAi).1).
  + rewrite (@hOff x hx); symmetry; apply: big1=> i _.
    have hNot : ~A i x by move=> h; exact: hx h.1.
    change (chi i x*:v i=0).
    by rewrite (@hChiOff i x hNot) scale0r.
- move=> x; case: (pselect (K x))=> hx.
  + have [i hAi] := (@hCover x).1 hx.
    rewrite hAi.2; exact: esym (@hOnCell i x hAi).2.
  + rewrite (@hOff x hx) (real_seminorm_zero hN.1); symmetry; apply: big1=> i _.
    have hNot : ~A i x by move=> h; exact: hx h.1.
    change (chi i x*N (v i)=0).
    by rewrite (@hChiOff i x hNot) mul0r.
Qed.
End FiniteCells.
