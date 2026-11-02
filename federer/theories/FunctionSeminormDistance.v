(** Federer (1969), 2.5.9, p. 100: the L1 distance used for continuous
    extension. Its pseudometric laws follow from the seminorm laws in
    2.4.12, pp. 86–87. Distinct total functions can have zero distance; no
    quotient is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import VectorFunctionLattice FunctionLatticeSeminormUP
  FunctionSeminormUnitBound ScalarLipschitzExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [function_seminorm_distance]: supporting distance
    for the extension in Federer 2.5.9, p. 100;
    N will be the already defined finite L1 seminorm. *)
Definition function_seminorm_distance (R : realType) (X : Type)
    (N : (X -> R) -> R) (f g : X -> R) := N (fun x => f x-g x).

(** Source for [function_seminorm_distance_laws]: pseudometric laws
    supporting Federer 2.5.9, p. 100, derived from 2.4.12, pp. 86–87 *)
Lemma function_seminorm_distance_laws (R : realType) (X : Type)
    (L : set (X -> R)) (N : (X -> R) -> R) :
  is_vector_function_lattice L -> is_finite_function_seminorm L N ->
  is_pseudometric_on_set L (function_seminorm_distance N).
Proof.
move=> hL hN; split.
- move=> f g hf hg; apply: (@function_seminorm_nonnegative R X L N hN).
  exact: (@vector_function_lattice_difference R X L hL f g hf hg).
- split.
  + move=> f hf; rewrite /function_seminorm_distance.
    have he : (fun x => f x-f x)=(fun _ : X => 0) by apply: funext=> x; rewrite subrr.
    by rewrite he (@function_seminorm_zero R X L N hL hN).
  + split.
    * move=> f g hf hg.
      have hd := @vector_function_lattice_difference R X L hL g f hg hf.
      have hh := @function_seminorm_scale R X L N hN (-1) _ hd.
      have he : (fun x => -1*(g x-f x))=(fun x => f x-g x).
        by apply: funext=> x; rewrite mulN1r opprB.
      by rewrite he normrN1 mul1r in hh.
    * move=> f g h hf hg hh.
      have hfg := @vector_function_lattice_difference R X L hL f g hf hg.
      have hgh := @vector_function_lattice_difference R X L hL g h hg hh.
      have ht := @function_seminorm_triangle R X L N hN _ _ hfg hgh.
      have he : (fun x => (f x-g x)+(g x-h x))=(fun x => f x-h x).
        by apply: funext=> x; rewrite addrA subrK.
      by rewrite he in ht.
Qed.

(** Source for [function_seminorm_distance_translate_right]: translation law
    supporting the additive extension in Federer 2.5.9, p. 100 *)
Lemma function_seminorm_distance_translate_right (R : realType) (X : Type)
    (N : (X -> R) -> R) (f g h : X -> R) :
  function_seminorm_distance N (fun x => f x+h x) (fun x => g x+h x)=function_seminorm_distance N f g.
Proof.
rewrite /function_seminorm_distance; congr (N _); apply: funext=> x.
by rewrite opprD addrA addrAC addrK.
Qed.

(** Source for [function_seminorm_distance_translate_left]: second
    translation law supporting Federer 2.5.9, p. 100 *)
Lemma function_seminorm_distance_translate_left (R : realType) (X : Type)
    (N : (X -> R) -> R) (f g h : X -> R) :
  function_seminorm_distance N (fun x => h x+f x) (fun x => h x+g x)=function_seminorm_distance N f g.
Proof.
rewrite /function_seminorm_distance; congr (N _); apply: funext=> x.
by rewrite [h x+f x]addrC [h x+g x]addrC opprD addrA addrAC addrK.
Qed.

(** Source for [function_seminorm_distance_scale]: homogeneity law
    supporting the continuous extension in Federer 2.5.9, p. 100 *)
Lemma function_seminorm_distance_scale (R : realType) (X : Type)
    (L : set (X -> R)) (N : (X -> R) -> R) :
  is_vector_function_lattice L -> is_finite_function_seminorm L N ->
  forall c f g, L f -> L g ->
    function_seminorm_distance N (fun x => c*f x) (fun x => c*g x)=
      `|c|*function_seminorm_distance N f g.
Proof.
move=> hL hN c f g hf hg.
have hd := @vector_function_lattice_difference R X L hL f g hf hg.
have hh := @function_seminorm_scale R X L N hN c _ hd.
have he : (fun x => c*(f x-g x))=(fun x => c*f x-c*g x).
  by apply: funext=> x; rewrite mulrBr.
by rewrite he in hh.
Qed.
