(** Federer (1969), 4.1.1, p. 344: a sequence
    that escapes every fixed compact support proves
    the corrected nonembedding assertion. This supporting
    topological argument uses only final and relative
    topology laws; it assumes no vector topology on D. *)
From mathcomp Require Import all_boot boolp functions classical_sets topology.
From Federer Require Import OpenFamilyTopologyUP OpenVectorTopologyUP OpenFamilyConvergence
  OpenFamilyFiniteAvoidance InitialOpenTopologyUP FinalOpenTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [final_topology_escaping_sequence_nonembedding]:
    a sequence converging in E while escaping every
    fixed-support step prevents D from having the
    E-relative topology, supporting the corrected
    assertion in Federer 4.1.1, p. 344. *)
Theorem final_topology_escaping_sequence_nonembedding
    (J:Type) (V:J->Type) (T:Type) (E:eqType)
    (OE:set (set E)) (OT:set (set T)) (OV:forall j,set (set (V j)))
    (inc:T->E) (j:forall i,V i->T) (r:forall i,V i->E)
    (s:nat->T) (z:T):
  is_open_family_topology OE ->open_family_hausdorff OE ->injective inc ->
  (forall i x,inc (j i x)=r i x) ->
  is_final_open_topology OV j OT ->
  (forall i,is_initial_open_topology OE (r i) (OV i)) ->
  (forall n,s n<>z) ->
  open_family_converges OE ((fun n=>inc (s n)) @ \oo) (inc z) ->
  (forall i,exists N,forall n,(N<=n)%N ->forall x:V i,j i x<>s n) ->
  ~is_initial_open_topology OE inc OT.
Proof.
move=>hOE hHaus hInc hFactor hFinal hStep hNe hCvg hEscape hRelative.
pose A:= [set t:T|forall n,t<>s n].
have hA:OT A.
  apply:(hFinal.2 A).2=>i.
  have [N hN]:=hEscape i.
  pose points:=map (fun n=>inc (s n)) (iota 0 N).
  pose B:=[set x:E|forall y,y \in points ->x<>y].
  have hB:OE B:=open_family_avoiding_finite_sequence hOE hHaus points.
  apply:((hStep i).2 _).2; exists B; split=>//.
  apply:funext=>x; apply:propext; split.
  - move=>h y /mapP [n hn ->] he.
    apply:(h n); apply:hInc; by rewrite hFactor.
  - move=>h n he.
    case:(leqP N n)=>[hLarge|hSmall].
    + exact:(hN n hLarge x he).
    + apply:(h (inc (s n))).
      * apply/mapP; exists n=>//; by rewrite mem_iota add0n leq0n.
      * by rewrite -hFactor he.
have hz:A z by move=>n he; exact:(hNe n (esym he)).
have [B [hB hAB]]:=(hRelative.2 A).1 hA.
have hzB:B (inc z) by move:hz; rewrite hAB.
have [N _ hN]:=hCvg B hB hzB.
have hsB:B (inc (s N)):=hN N (leqnn N).
have hsA:A (s N) by rewrite hAB.
exact:(hsA N (erefl _)).
Qed.
