(** Federer (1969), 2.5.9, p. 100: linearity of the extension from the
    positive cone. The corrected positive density is erratum p. 2, book p.
    100 line 22. These algebraic consequences use only the positive
    functional's laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws VectorFunctionLattice
  FunctionLatticeSeminormUP PositiveDifferenceFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_difference_functional_additive]:
    supporting additive extension in Federer 2.5.9, p. 100,
    from the corrected positive cone. *)
Lemma positive_difference_functional_additive (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_vector_function_lattice L) (B : (X -> R) -> R) :
  (forall f g, positive_function_lattice L f -> positive_function_lattice L g ->
    B (fun x => f x+g x)=B f+B g) ->
  forall f g, L f -> L g ->
    positive_difference_functional B (fun x => f x+g x)=
      positive_difference_functional B f+positive_difference_functional B g.
Proof.
move=> hB f g hf hg.
pose p x := Order.max (f x) 0; pose q x := Order.max (-f x) 0.
pose r x := Order.max (g x) 0; pose s x := Order.max (-g x) 0.
have [hp hq] := @positive_parts_membership R X L hL.1 f hf.
have [hr hs] := @positive_parts_membership R X L hL.1 g hg.
have hpos := @positive_function_lattice_laws R X L hL.1.
have hpr := @function_lattice_add R X _ hpos p r hp hr.
have hqs := @function_lattice_add R X _ hpos q s hq hs.
have hadd := @function_lattice_add R X L hL.1 f g hf hg.
have he : (fun x => (p x+r x)-(q x+s x))=(fun x => f x+g x).
  apply: funext=> x; rewrite opprD addrACA.
  have hfpart : p x-q x=f x := congr1 (fun u => u x) (positive_parts_difference f).
  have hgpart : r x-s x=g x := congr1 (fun u => u x) (positive_parts_difference g).
  by rewrite hfpart hgpart.
rewrite (@positive_difference_functional_value R X L hL.1 B hB _ _ _ hadd hpr hqs he).
by rewrite (hB p r hp hr) (hB q s hq hs) opprD addrACA.
Qed.

(** Source for [positive_difference_functional_nonnegative_scale]:
    positive homogeneity supporting Federer 2.5.9, p. 100.
    Zero scalars and zero functions are included. *)
Lemma positive_difference_functional_nonnegative_scale (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_vector_function_lattice L) (B : (X -> R) -> R) :
  (forall f g, positive_function_lattice L f -> positive_function_lattice L g ->
    B (fun x => f x+g x)=B f+B g) ->
  (forall c f, 0 <= c -> positive_function_lattice L f ->
    B (fun x => c*f x)=c*B f) ->
  forall c f, 0 <= c -> L f ->
    positive_difference_functional B (fun x => c*f x)=c * positive_difference_functional B f.
Proof.
move=> hB hscale c f hc hf.
pose p x := Order.max (f x) 0; pose q x := Order.max (-f x) 0.
have [hp hq] := @positive_parts_membership R X L hL.1 f hf.
have hpos := @positive_function_lattice_laws R X L hL.1.
have hcp := @function_lattice_scale R X _ hpos c p hc hp.
have hcq := @function_lattice_scale R X _ hpos c q hc hq.
have hcf := hL.2.2 c f hf.
have he : (fun x => c * p x-c * q x)=(fun x => c*f x).
  apply: funext=> x; rewrite -mulrBr.
  have hh : p x-q x=f x := congr1 (fun u => u x) (positive_parts_difference f).
  by rewrite hh.
rewrite (@positive_difference_functional_value R X L hL.1 B hB _ _ _ hcf hcp hcq he).
by rewrite (hscale c p hc hp) (hscale c q hc hq) -mulrBr.
Qed.

(** Source for [positive_difference_functional_negation]:
    negative homogeneity supporting Federer 2.5.9, p. 100;
    negation exchanges the positive and negative parts. *)
Lemma positive_difference_functional_negation (R : realType) (X : Type)
    (B : (X -> R) -> R) (f : X -> R) :
  positive_difference_functional B (fun x => -f x)= -positive_difference_functional B f.
Proof.
rewrite /positive_difference_functional.
have he : (fun x => Order.max (- -f x) 0)=(fun x => Order.max (f x) 0).
  by apply: funext=> x; rewrite opprK.
by rewrite he opprB.
Qed.

(** Source for [positive_difference_functional_linear]: full
    real linearity in the extension step of Federer 2.5.9,
    p. 100, deduced from the positive cone's laws. *)
Theorem positive_difference_functional_linear (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_vector_function_lattice L) (B : (X -> R) -> R) :
  (forall f g, positive_function_lattice L f -> positive_function_lattice L g ->
    B (fun x => f x+g x)=B f+B g) ->
  (forall c f, 0 <= c -> positive_function_lattice L f ->
    B (fun x => c*f x)=c*B f) ->
  is_linear_functional_on_functions L (positive_difference_functional B).
Proof.
move=> hB hscale; split; first exact: (@positive_difference_functional_additive R X L hL B hB).
move=> c f hf; case: (leP 0 c)=> hc.
- exact: (@positive_difference_functional_nonnegative_scale R X L hL B hB hscale c f hc hf).
- have hn : 0 <= -c by rewrite oppr_ge0; exact: ltW hc.
  have he : (fun x => c*f x)=(fun x => -((-c)*f x)).
    by apply: funext=> x; rewrite mulNr opprK.
  rewrite he positive_difference_functional_negation.
  by rewrite (@positive_difference_functional_nonnegative_scale R X L hL B hB hscale (-c) f hn hf) mulNr opprK.
Qed.
