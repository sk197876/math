(** Federer (1969), 3.2.22, p. 259: supporting
    Borel representatives of scalar differential observables.
    An exact default outside their Borel domains permits
    composition with the chart inverses without pulling back
    arbitrary completed-measure representatives. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed PartialZeroExtensionUP PartialZeroExtensionSealed
  TopologicalBorel BorelFamilyBasic BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_partial_total_extension_exists]:
    supporting Borel approximation in Federer 3.2.22,
    p. 259, using the Borel inverse-image laws of
    2.2.14, p. 70, and the total-extension convention
    of 2.3.2, p. 73. Preserve every actual value
    and use a specified default at every undefined point.
    Existing opaque zero-extension and total-extension laws
    prove existence; no new global choice or project axiom
    is introduced. *)
Theorem borel_partial_total_extension_exists (X Y:topologicalType)
    (f:partial_function X Y) (y0:Y):
  (forall U:set Y,open U ->borel_set (partial_function_preimage f U)) ->
  exists h:X->Y,is_partial_function_total_extension f h /\
    (forall x,~partial_function_domain f x ->h x=y0) /\ is_borel_function h.
Proof.
move=>hBorel.
pose A:=partial_function_domain f.
pose g:=@PartialZeroExtension.value X Y y0 A f.
have hg:=@PartialZeroExtension.laws X Y y0 A f.
pose h:=@PartialFunctionExtension.value X Y g y0.
have hh:=@PartialFunctionExtension.laws X Y g y0.
have hAgree:is_partial_function_total_extension f h.
  move=>x y hxy; apply:hh; apply:(hg x y).2; left; split; last exact hxy.
  by exists y.
have hDefault x:~A x ->h x=y0.
  move=>hx; apply:hh; apply:(hg x y0).2; right; by split.
have hAB:borel_set A.
  have hD:=hBorel setT openT; by rewrite partial_function_preimage_whole in hD.
exists h; split; first exact hAgree; split; first exact hDefault.
move=>U hU.
have hEq:h @^-1` U=partial_function_preimage f U `|` [set x|~A x /\ U y0].
  apply/seteqP; split=>x.
  - move=>hx; have [ha|ha]:=pselect (A x).
    + left; have [y hy]:=ha; exists y; split; first exact hy.
      by rewrite -(hAgree x y hy).
    + right; split; first exact ha; by rewrite -(hDefault x ha).
  - move=>[[y [hy hUy]]|[hx hUy]].
    + change (U (h x)); by rewrite (hAgree x y hy).
    + change (U (h x)); by rewrite (hDefault x hx).
have hElse:borel_set [set x|~A x /\ U y0].
  have [hy|hy]:=pselect (U y0).
  - have hSet:[set x|~A x /\ U y0]=~` A.
      apply/seteqP; split=>x; first by move=>[].
      by move=>hx; split.
    rewrite hSet; exact:borel_set_complement hAB.
  - have hSet:[set x|~A x /\ U y0]=set0.
      apply/seteqP; split=>[x [_ hx]|x []]; exact:hy hx.
    rewrite hSet; exact:open_borel_set open0.
rewrite hEq; exact:(borel_family_binary_union (borel_sets_family _) (hBorel U hU) hElse).
Qed.
