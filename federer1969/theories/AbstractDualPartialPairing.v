(** Federer (1969), 4.1.5, p. 350:
    the original integral pairing with an actual
    abstract dual field retains the vector function's
    conull partial domain. Existing graph pairing
    and postcomposition express the canonical operation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  ExtendedRealOrderTopology SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [abstract_dual_partial_pairing]:
    the literal <f,xi> for the L1 extension
    of S in Federer 4.1.5, p. 350.
    No value is assigned outside the original f domain. *)
Definition abstract_dual_partial_pairing (R:realType) (X:choiceType)
    (Y D:lmodType R) (ed:Hom D (Hom Y R^o)) (xi:X->D)
    (f:partial_function X Y):partial_function X (extended_real_line R):=
  @partial_function_postcompose X (Y*D) (extended_real_line R)
    (partial_function_pair f (partial_function_total xi))
    (fun p=>(ed p.2 p.1)%:E).

(** Source for [abstract_dual_partial_pairing_graph]:
    exact original-domain graph of the pairing in
    Federer 4.1.5, p. 350. *)
Lemma abstract_dual_partial_pairing_graph (R:realType) (X:choiceType)
    (Y D:lmodType R) (ed:Hom D (Hom Y R^o)) (xi:X->D)
    (f:partial_function X Y) x z:
  partial_function_graph (abstract_dual_partial_pairing ed xi f) x z <->
    exists y,partial_function_graph f x y /\ (ed (xi x) y)%:E=z.
Proof.
split.
- move=>[[y a] [[hy ha] he]]; exists y; split=>//.
  by rewrite (ha:xi x=a).
- move=>[y [hy he]]; exists (y,xi x); by split=>//; split.
Qed.

(** Source for [abstract_dual_partial_pairing_total_graph]:
    the original total test pairing is the same
    finite real integrand, Federer 4.1.5, p. 350. *)
Lemma abstract_dual_partial_pairing_total_graph (R:realType) (X:choiceType)
    (Y D:lmodType R) (ed:Hom D (Hom Y R^o)) (xi:X->D) (f:X->Y) x z:
  partial_function_graph (abstract_dual_partial_pairing ed xi (partial_function_total f)) x z <->
    partial_function_graph (real_total_integrand (fun x=>ed (xi x) (f x))) x z.
Proof.
rewrite abstract_dual_partial_pairing_graph real_total_integrand_graph.
split.
- by move=>[y [<- he]].
- move=>he; exists (f x); by split.
Qed.
