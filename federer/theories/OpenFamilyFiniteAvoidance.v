(** Federer (1969), 4.1.1, p. 344: a
    finite set is closed in the Hausdorff smooth
    topology. This supporting open-set fact is used
    in the corrected test-space nonembedding proof. *)
From mathcomp Require Import all_boot boolp functions classical_sets.
From Federer Require Import OpenFamilyTopologyUP OpenFamilyTopologyLaws OpenVectorTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_family_avoiding_point]: point
    complements are open in a Hausdorff topology,
    supporting Federer 4.1.1, p. 344. *)
Lemma open_family_avoiding_point (X:Type) (O:set (set X)):
  is_open_family_topology O ->open_family_hausdorff O ->forall a:X,O [set x|x<>a].
Proof.
move=>hO hHaus a; apply:(@open_family_locally_open X O [set x|x<>a] hO).2=>x hx.
have [V [W [hV [hW [hxV [haW hDis]]]]]]:=hHaus x a hx.
exists V; split=>//; split=>// y hy hya.
apply:(hDis a); split; last exact haW; by rewrite -hya.
Qed.

(** Source for [open_family_avoiding_finite_sequence]: the
    complement of a finite list of points is open,
    supporting the corrected nonembedding proof in
    Federer 4.1.1, p. 344. Repetitions in
    the list are allowed. *)
Theorem open_family_avoiding_finite_sequence (X:eqType) (O:set (set X)):
  is_open_family_topology O ->open_family_hausdorff O ->forall s:seq X,
    O [set x|forall y,y \in s ->x<>y].
Proof.
move=>hO hHaus; elim=>[|a s ih].
- have hEq:[set x:X|forall y,y \in [::] ->x<>y]=setT.
    apply:funext=>x; apply:propext; by split=>// _ y; rewrite in_nil.
  by rewrite hEq; exact:open_family_whole hO.
- have hEq:[set x:X|forall y,y \in a::s ->x<>y]=
    [set x:X|x<>a] `&` [set x:X|forall y,y \in s ->x<>y].
    apply:funext=>x; apply:propext; split.
    + move=>h; split; first exact:(h a (mem_head a s)).
      move=>y hy; apply:h; by rewrite in_cons hy orbT.
    + move=>[ha hs] y; rewrite in_cons=>/orP [/eqP ->|hy]; [exact ha|exact:hs y hy].
  rewrite hEq; exact (@open_family_intersection X O hO [set x:X|x<>a]
    [set x:X|forall y,y \in s ->x<>y] (@open_family_avoiding_point X O hO hHaus a) ih).
Qed.
