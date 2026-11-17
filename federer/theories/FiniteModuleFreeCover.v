(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328, and the finite coefficient module of (8), p. 329.
    Extract the existing finite-synthesis connection from the
    Noetherian module proof; do not assume a basis for a ring module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP RingSubmoduleLinear RingFiniteSynthesis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_module_free_cover]: supporting connection
    for the finite original coefficient modules in Federer 3.4.8(8),
    p. 329, used to investigate the stronger auxiliary sentence
    in (5), p. 328. A finite module has a finite free cover;
    this asserts neither injectivity nor a module basis. *)
Theorem finite_module_free_cover (A:nzRingType) (V:lmodType A):
  is_finitely_generated_ring_submodule (setT:set V) ->
  exists n,exists e:'I_n->V,forall x:V,
    exists c:{ffun 'I_n->A^o},ring_finite_synthesis e c = x.
Proof.
move=>[F hF].
pose e (i:'I_(size F)):=nth (0:V) F i.
pose f:=GRing.Linear.clone _ _ _ _ (@ring_finite_synthesis A V (size F) e) _.
have hWhole:is_ring_submodule (setT:set {ffun 'I_(size F)->A^o}) by constructor.
have hImage:=ring_submodule_linear_image f hWhole.
have hCover:(setT:set V) `<=` f @` setT.
  apply:(generated_ring_submodule_minimal hF hImage)=>x hx.
  have hi:(index x F<size F)%N by rewrite index_mem.
  pose j:'I_(size F):=Ordinal hi.
  exists [ffun i:'I_(size F)=>if i==j then (1:A) else 0];first exact:I.
  change (ring_finite_synthesis e [ffun i=>if i==j then (1:A) else 0] = x).
  by rewrite ring_finite_synthesis_generator /e /j /= (nth_index 0 hx).
exists (size F),e=>x.
have [c _ hc]:=hCover x I;by exists c.
Qed.
