(** Supporting Federer (1969), 2.10.46, p. 204: the scalar fibre-counting
    step of Freilich (1950), Theorem 4.5, Part 4, pp. 245–247. After the
    adapted projection chart, a point over y has scalar coordinate a*t+b(x).
    For a nonzero, each eligible x determines exactly one t. The proof uses
    the abstract counting measure, including infinite fibres. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MappingMultiplicity CountingMeasure CountingInjectionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [affine_cylinder_fibre_count]: supporting
    exact counting identity in the cylinder argument of
    2.10.46, p. 204; Freilich (1950), Part 4
    of Theorem 4.5, pp. 245–247. The supplied
    map is specified by its affine coordinate law. No
    measurability or finiteness assumption is needed for this
    set-theoretic step; nonzero stretching is essential. *)
Theorem affine_cylinder_fibre_count (R : realType) (X Y : choiceType)
    (f : R*X -> R*Y) (q : X -> Y) (a : R) (b : X -> R)
    (T : set R) (V : set X) (w : R) (y : Y) :
  a!=0%R -> (forall t x, f (t,x)=((a*t+b x)%R,q x)) ->
  @mapping_multiplicity R [the choiceType of (R*X)%type] (R*Y)%type f (T `*` V) (w,y)=
    counting_measure (R:=R) [set x | V x /\ q x=y /\ T ((w-b x)/a)%R].
Proof.
move=> ha hf; rewrite /mapping_multiplicity; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@counting_measure_injection_bound R [the choiceType of (R*X)%type] X
    (mapping_fibre f (T `*` V) (w,y)) _ snd).
  + move=> [t x] [[ht hx] he]; have hs := congr1 fst he; have hq := congr1 snd he.
    rewrite hf /= in hs hq; split=> //; split=> //.
    have hval : ((w-b x)/a)%R=t by rewrite -hs addrK [(a*t)%R]mulrC mulfK.
    by rewrite hval.
  + move=> [t x] [u z] [[ht hx] he] [[hu hz] hd] /= hez; subst z.
    have hs := congr1 fst he; have hr := congr1 fst hd; rewrite !hf /= in hs hr.
    have htu := congr1 (fun r : R=>((r-b x)/a)%R) (eq_trans hs (esym hr)).
    rewrite !addrK [(a*t)%R]mulrC [(a*u)%R]mulrC !mulfK // in htu.
    by subst u.
- apply: (@counting_measure_injection_bound R X [the choiceType of (R*X)%type]
    _ (mapping_fibre f (T `*` V) (w,y)) (fun x=>(((w-b x)/a)%R,x))).
  + move=> x [hx [hq ht]]; split; first by split.
    rewrite hf hq; congr (_, _).
    by rewrite mulrC divfK // subrK.
  + move=> x z hx hz he; exact (congr1 snd he).
Qed.
