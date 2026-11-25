(** Federer (1969), 2.5.9, p. 100: extend the positive cone functional to
    the full total L1 space by differences. The positive-cone density
    correction is erratum p. 2, book p. 100 line 22. The
    difference-consistency calculation below is supporting algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws VectorFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_parts_difference]: the parts decomposition from
    Federer 2.5.1, p. 91, supporting 2.5.9, p. 100 *)
Lemma positive_parts_difference (R : realType) (X : Type) (f : X -> R) :
  (fun x => Order.max (f x) 0-Order.max (-f x) 0)=f.
Proof.
apply: funext=> x; case: (leP 0 (f x))=> hx.
- by rewrite max_r ?oppr_le0 // subr0.
- by rewrite max_l ?oppr_ge0 ?ltW // sub0r opprK.
Qed.

(** Source for [positive_parts_membership]: membership and positivity of the
    two parts used in Federer 2.5.9, p. 100 *)
Lemma positive_parts_membership (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) :
  L f -> positive_function_lattice L (fun x => Order.max (f x) 0) /\
    positive_function_lattice L (fun x => Order.max (-f x) 0).
Proof.
move=> hf; split; split.
- exact: (@function_lattice_positive_part R X L hL f hf).
- by move=> x; rewrite le_max lexx orbT.
- exact: (@function_lattice_negative_part R X L hL f hf).
- by move=> x; rewrite le_max lexx orbT.
Qed.

(** Source for [positive_difference_functional]: supporting
    positive/negative-parts expression for the extension in Federer
    2.5.9, p. 100. Its representation-independence is proved below. *)
Definition positive_difference_functional (R : realType) (X : Type)
    (B : (X -> R) -> R) (f : X -> R) :=
  B (fun x => Order.max (f x) 0)-B (fun x => Order.max (-f x) 0).

(** Source for [positive_difference_consistent]: supporting
    independence from the chosen positive difference in Federer
    2.5.9, p. 100. Only addition on the positive cone is used. *)
Lemma positive_difference_consistent (R : realType) (X : Type)
    (L : set (X -> R)) (B : (X -> R) -> R) :
  (forall f g, positive_function_lattice L f -> positive_function_lattice L g ->
    B (fun x => f x+g x)=B f+B g) ->
  forall p q r s, positive_function_lattice L p -> positive_function_lattice L q ->
    positive_function_lattice L r -> positive_function_lattice L s ->
    (fun x => p x-q x)=(fun x => r x-s x) -> B p-B q=B r-B s.
Proof.
move=> hB p q r s hp hq hr hs he.
have headd : (fun x => p x+s x)=(fun x => r x+q x).
  apply: funext=> x; have hv := congr1 (fun f => f x) he.
  have hpv : p x=r x-s x+q x by apply/eqP; rewrite -subr_eq; exact/eqP.
  by rewrite hpv addrAC subrK.
have hb := congr1 B headd; rewrite (hB p s hp hs) (hB r q hr hq) in hb.
have hpv : B p=B r+B q-B s by rewrite -hb addrK.
by rewrite hpv addrAC addrK.
Qed.

(** Source for [positive_difference_functional_value]: the
    extension in Federer 2.5.9, p. 100, evaluates every
    positive decomposition consistently; no quotient representatives
    or construction-specific facts occur in this identity. *)
Lemma positive_difference_functional_value (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (B : (X -> R) -> R) :
  (forall f g, positive_function_lattice L f -> positive_function_lattice L g ->
    B (fun x => f x+g x)=B f+B g) ->
  forall f p q, L f -> positive_function_lattice L p -> positive_function_lattice L q ->
    (fun x => p x-q x)=f -> positive_difference_functional B f=B p-B q.
Proof.
move=> hB f p q hf hp hq he.
have [hfp hfn] := @positive_parts_membership R X L hL f hf.
apply: (@positive_difference_consistent R X L B hB _ _ p q hfp hfn hp hq).
by rewrite positive_parts_difference he.
Qed.
