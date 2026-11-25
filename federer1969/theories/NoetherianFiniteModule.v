(** Federer (1969), 3.4.7, p. 325: the
    submodule M intersect I is finitely generated because
    M has finitely many generators over the transverse
    Noetherian ring. This proof expands the printed module
    reference through an actual finite free cover. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions.
From Federer Require Import CommutativeIdealUP RingSubmoduleUP RingSubmoduleLinear
  NoetherianModuleUP NoetherianFiniteFreeModule NoetherianLinearCover RingFiniteSynthesis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_submodule_of_finite_module]:
    the finite-module assertion used for M intersect I
    in 3.4.7, p. 325. Every original submodule
    of a finitely generated module over a Noetherian
    ring has finite generators; no basis is assumed. *)
Theorem noetherian_submodule_of_finite_module (A:comNzRingType) (V:lmodType A)
    (M N:set V):
  is_noetherian_commutative_ring A ->
  is_finitely_generated_ring_submodule M ->
  is_ring_submodule N ->N `<=` M ->is_finitely_generated_ring_submodule N.
Proof.
move=>hA [F hF] hN hNM.
pose e (i:'I_(size F)):=nth (0:V) F i.
pose f:=GRing.Linear.clone _ _ _ _ (@ring_finite_synthesis A V (size F) e) _.
have hWhole:is_ring_submodule (setT: set {ffun 'I_(size F)->A^o}).
  by constructor.
have hImage:=ring_submodule_linear_image f hWhole.
have hCover:M `<=` f @` setT.
  apply:(generated_ring_submodule_minimal hF hImage)=>x hx.
  have hi:(index x F<size F)%N by rewrite index_mem.
  pose j:'I_(size F):=Ordinal hi.
  exists [ffun i:'I_(size F)=>if i==j then (1:A) else 0];first exact:Logic.I.
  change (ring_finite_synthesis e [ffun i=>if i==j then (1:A) else 0] = x).
  by rewrite ring_finite_synthesis_generator /e /j /=  (nth_index 0 hx).
apply:(@noetherian_module_linear_cover A [the lmodType A of {ffun 'I_(size F)->A^o}] V
  f N (@noetherian_finite_free_module A hA (size F)) hN).
move=>x hx;have [u _ hu]:=hCover x (hNM x hx);by exists u.
Qed.
