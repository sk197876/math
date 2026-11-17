(** Federer (1969), 3.4.8(8), p. 329:
    the nested finite simple extensions give a finite
    module over the original coefficient ring. Use
    the existing least-submodule laws and scalar
    restriction; products of finite generator families
    prove existence of a finite generator family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ring_module_tower]: finite
    generation is transitive along the original
    coefficient-ring tower, supporting integral dependence
    in 3.4.8(8), p. 329. Each original module
    retains its abstract least-submodule specification. *)
Theorem finite_ring_module_tower (A B:comNzRingType) (phi:{rmorphism A->B})
  (V:lmodType B):
  @is_finitely_generated_ring_submodule A
    [the lmodType A of ring_restricted_space phi B^o] setT ->
  @is_finitely_generated_ring_submodule B V setT ->
  @is_finitely_generated_ring_submodule A
    [the lmodType A of ring_restricted_space phi V] setT.
Proof.
move=>[F hF] [G hG].
pose W:=[the lmodType A of ring_restricted_space phi V].
pose products:seq W:=flatten (map (fun b:B=>map (fun v:V=>b*:v) G) F).
exists products;constructor.
- by constructor.
- by move=>x hx.
- move=>N hN hProducts.
  have hGenerators (v:V) (hV:v \in G):forall b:B,N (b*:v).
    pose P:set [the lmodType A of ring_restricted_space phi B^o]:=fun b=>N (b*:v).
    have hP:is_ring_submodule P.
      constructor.
      + change (N (0*:v));rewrite scale0r;exact:ring_submodule_zero hN.
      + move=>a b hA hB;change (N ((a+b)*:v));rewrite scalerDl.
        exact:(@ring_submodule_add A W N hN _ _ hA hB).
      + move=>b hB;change (N ((-b)*:v));rewrite scaleNr.
        exact:(@ring_submodule_opp A W N hN _ hB).
      + move=>a b hB;change (N ((phi a*b)*:v));rewrite -scalerA.
        exact:(@ring_submodule_scale A W N hN a (b*:v) hB).
    have hAll:setT `<=` P.
      apply:(generated_ring_submodule_minimal hF hP)=>b hB.
      apply:hProducts;rewrite /products;apply/flattenP.
      exists (map (fun w:V=>b*:w) G).
      * apply/mapP;by exists b.
      * apply/mapP;by exists v.
    move=>b;exact:hAll b Logic.I.
  pose S:set V:=fun v=>forall b:B,N (b*:v).
  have hS:is_ring_submodule S.
    constructor.
    + move=>b;rewrite scaler0;exact:ring_submodule_zero hN.
    + move=>v w hV hW b;rewrite scalerDr.
      exact:(@ring_submodule_add A W N hN _ _ (hV b) (hW b)).
    + move=>v hV b;rewrite scalerN.
      exact:(@ring_submodule_opp A W N hN _ (hV b)).
    + move=>a v hV b;rewrite scalerA;exact:hV (b*a).
  have hAll:setT `<=` S.
    apply:(generated_ring_submodule_minimal hG hS)=>v hV.
    exact:hGenerators v hV.
  move=>v _;have hOne:=hAll v Logic.I 1.
  by rewrite scale1r in hOne.
Qed.
