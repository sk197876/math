(** Federer (1969), 3.2.25, p. 261: glue the
    orientations on disjoint compact chart images. State the
    graph law before proving existence; every chosen witness
    remains local to an opaque existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic TopologicalBorel BorelFamilyBasic
  BorelFunctionUP MeasureUP MeasureRestriction MeasureAlmostUP MeasurableFunctionUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_borel_partial_gluing]: the piecewise
    definition of T on the disjoint psi_i(K_i) in
    3.2.25, p. 261, expressed as an exact graph law.
    It neither chooses an index nor asserts a value outside
    the union of the specified pieces. *)
Definition is_borel_partial_gluing (X Y I:Type) (D:set I)
    (B:I->set X) (f:I->X->Y) (T:partial_function X Y):=
  forall x y,partial_function_graph T x y <->exists i,D i /\B i x /\f i x=y.

(** Source for [borel_partial_gluing_exists]: the existence
    and measurability of the piecewise T in 3.2.25,
    p. 261. Disjointness proves single-valuedness; countable
    Borel unions prove every open inverse image is Borel.
    No target inhabitant or outside default value is needed. *)
Theorem borel_partial_gluing_exists (X Y:topologicalType) (I:choiceType)
    (D:set I) (B:I->set X) (f:I->X->Y):
  countable D ->(forall i,D i ->borel_set (B i)) ->
  (forall i,D i ->is_borel_function (f i)) ->
  (forall i j,D i ->D j ->i!=j ->forall x,B i x ->B j x ->False) ->
  exists T:partial_function X Y,
    is_borel_partial_gluing D B f T /\
    partial_function_domain T=\bigcup_(i in D) B i /\
    forall U:set Y,open U ->borel_set (partial_function_preimage T U).
Proof.
move=>hCount hB hF hDisjoint.
pose G:=fun x y=>exists i,D i /\B i x /\f i x=y.
have hSingle x y z:G x y ->G x z ->y=z.
  move=>[i [hi [hix hiy]]] [j [hj [hjx hjz]]].
  have [hIJ|hIJ]:=eqVneq i j.
  - rewrite -hIJ in hjz; exact:(eq_trans (esym hiy) hjz).
  - exfalso; exact:(hDisjoint i j hi hj hIJ x hix hjx).
pose T:=@Build_partial_function X Y G hSingle.
have hGraph:is_borel_partial_gluing D B f T by move=>x y.
have hDomain:partial_function_domain T=\bigcup_(i in D) B i.
  apply/seteqP; split=>x.
  - by move=>[y [i [hi [hix _]]]]; exists i.
  - move=>[i hi hix]; exists (f i x); exists i; by split; last split.
exists T; split; first exact hGraph; split; first exact hDomain.
move=>U hU.
have hPre:partial_function_preimage T U=\bigcup_(i in D) (B i `&` (f i @^-1` U)).
  apply/seteqP; split=>x.
  - move=>[y [[i [hi [hix hiy]]] hUy]]; exists i; first exact hi.
    split; first exact hix; change (U (f i x)); by rewrite hiy.
  - move=>[i hi [hix hUi]]; exists (f i x); split; last exact hUi.
    exists i; by split; last split.
rewrite hPre; apply:(borel_set_countable_union hCount)=>i hi.
exact:(borel_family_binary_intersection (borel_sets_family X) (hB i hi) (hF i hi U hU)).
Qed.

(** Source for [borel_partial_measurable_on]: the H^m
    restricted-to-W measurability required in 3.2.25,
    p. 261. Open preimages remain measurable after
    arbitrary source-measure restriction, even if W itself
    is not measurable. The conull domain is retained exactly. *)
Lemma borel_partial_measurable_on (R:realType) (X Y:topologicalType)
    (phi:set X->\bar R) (W:set X) (T:partial_function X Y):
  is_measure phi ->is_borel_regular_measure phi ->
  (forall U:set Y,open U ->borel_set (partial_function_preimage T U)) ->
  phi (W `\` partial_function_domain T)=0 ->
  is_measure_measurable_function (measure_restrict phi W) T.
Proof.
move=>hPhi hRegular hBorel hDomain; constructor.
- exact hDomain.
- move=>U hU; apply:measure_restrict_measurable.
  exact:(borel_regular_borel_measurable hPhi hRegular (hBorel U hU)).
Qed.
