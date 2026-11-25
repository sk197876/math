(** Federer (1969), 3.4.5, pp. 319–320: compatible
    operations on representatives induce unique operations on germs. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import LocalGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Lifting.
Variable X:topologicalType.
Variable Y:Type.
Variable P:choiceType.
Variable value:P->X->Y.
Variable a:X.
Variable G:choiceType.
Variable germ:P->G.
Hypothesis hG:is_local_germ_space value a germ.

(** Source for [local_germ_unary_lift_exists]: unary operations
    descend through the original neighbourhood equivalence,
    3.4.5, pp. 319–320. Only compatibility is required. *)
Theorem local_germ_unary_lift_exists (op:P->P):
  (forall f g,locally_equal_at a (value f) (value g) ->
    locally_equal_at a (value (op f)) (value (op g))) ->
  exists u:G->G,forall f,u (germ f)=germ (op f).
Proof.
move=>hCompatible.
have hRepresentative alpha:exists f,germ f=alpha:=local_germ_representative hG alpha.
pose repr alpha:=projT1 (cid (hRepresentative alpha)).
have hRepr alpha:germ (repr alpha)=alpha:=projT2 (cid (hRepresentative alpha)).
exists (fun alpha=>germ (op (repr alpha)))=>f.
apply/(local_germ_equality hG);apply:hCompatible.
apply/(local_germ_equality hG);exact:hRepr.
Qed.

(** Source for [local_germ_unary_lift_unique]: the induced
    operation is determined by its values on representatives,
    3.4.5, pp. 319–320. *)
Lemma local_germ_unary_lift_unique (op:P->P) (u v:G->G):
  (forall f,u (germ f)=germ (op f)) ->
  (forall f,v (germ f)=germ (op f)) ->u=v.
Proof.
move=>hU hV;apply:funext=>alpha.
have [f <-]:=local_germ_representative hG alpha.
by rewrite hU hV.
Qed.

(** Source for [local_germ_binary_lift_exists]: binary operations
    descend through the original local equivalence, 3.4.5,
    pp. 319–320. The operation is specified by its representative
    equation; selected representatives stay local to this existence proof. *)
Theorem local_germ_binary_lift_exists (op:P->P->P):
  (forall f f' g g',
    locally_equal_at a (value f) (value f') ->
    locally_equal_at a (value g) (value g') ->
    locally_equal_at a (value (op f g)) (value (op f' g'))) ->
  exists u:G->G->G,forall f g,u (germ f) (germ g)=germ (op f g).
Proof.
move=>hCompatible.
have hRepresentative alpha:exists f,germ f=alpha:=local_germ_representative hG alpha.
pose repr alpha:=projT1 (cid (hRepresentative alpha)).
have hRepr alpha:germ (repr alpha)=alpha:=projT2 (cid (hRepresentative alpha)).
exists (fun alpha beta=>germ (op (repr alpha) (repr beta)))=>f g.
apply/(local_germ_equality hG);apply:hCompatible;
  apply/(local_germ_equality hG);exact:hRepr.
Qed.

(** Source for [local_germ_binary_lift_unique]: induced binary
    operations are uniquely determined by representatives,
    3.4.5, pp. 319–320. *)
Lemma local_germ_binary_lift_unique (op:P->P->P) (u v:G->G->G):
  (forall f g,u (germ f) (germ g)=germ (op f g)) ->
  (forall f g,v (germ f) (germ g)=germ (op f g)) ->u=v.
Proof.
move=>hU hV;apply:funext=>alpha;apply:funext=>beta.
have [f <-]:=local_germ_representative hG alpha.
have [g <-]:=local_germ_representative hG beta.
by rewrite hU hV.
Qed.
End Lifting.
