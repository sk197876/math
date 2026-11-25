(** Federer (1969), 2.3.2, p. 74: partial numerical operations can be
    extended across their exceptional domain to Borel maps. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalBorel BorelFamilyBasic BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_continuous_region_preimage]: Supporting Federer 2.3.2,
    p. 74.Continuity is required only at points of the Borel region D. *)
Lemma borel_continuous_region_preimage (X Y : topologicalType)
    (D : set X) (f : X -> Y) : borel_set D ->
  (forall x, D x -> {for x, continuous f}) ->
  forall U, open U -> borel_set (D `&` (f @^-1` U)).
Proof.
move=> hD hf U hU.
have he : D `&` (f @^-1` U) = D `&` (f @^-1` U)°.
  apply/seteqP; split=> x [hd hx]; split=> //.
  - apply: (hf x hd); by rewrite openE in hU; exact: hU _ hx.
  - exact: nbhs_singleton hx.
rewrite he; apply: (borel_family_binary_intersection (borel_sets_family X))=> //.
exact: open_borel_set (open_interior _).
Qed.

(** Source for [borel_continuous_region_extension]: supporting constant
    extension of a numerical operation off its defined Borel domain; this
    implements the numerical-closure argument in Federer 2.3.2, p. 74. *)
Theorem borel_continuous_region_extension (X Y : topologicalType)
    (D : set X) (f : X -> Y) (c : Y) : borel_set D ->
  (forall x, D x -> {for x, continuous f}) ->
  is_borel_function (fun x => if pselect (D x) then f x else c).
Proof.
move=> hD hf U hU.
have hA := @borel_continuous_region_preimage X Y D f hD hf U hU.
case: (pselect (U c))=> hc.
- have he : (fun x => if pselect (D x) then f x else c) @^-1` U =
      (D `&` (f @^-1` U)) `|` ~` D.
    apply/seteqP; split=> x; rewrite /preimage /=; case: (pselect (D x))=> hx.
    + by move=> hu; left; split.
    + by move=> _; right.
    + by move=> [[_ hu]|hn] //; exact: False_ind (hn hx).
    + by move=> _.
  rewrite he; exact: (borel_family_binary_union (borel_sets_family X) hA (borel_set_complement hD)).
- have he : (fun x => if pselect (D x) then f x else c) @^-1` U = D `&` (f @^-1` U).
    apply/seteqP; split=> x; rewrite /preimage /=; case: (pselect (D x))=> hx.
    + by move=> hu; split.
    + by move=> hu; exfalso; exact: hc hu.
    + by move=> [_ hu].
    + by move=> [hd _]; exfalso; exact: hx hd.
  by rewrite he.
Qed.
