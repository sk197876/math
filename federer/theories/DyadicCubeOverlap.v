(** Federer (1969), 2.10.47(1), pp. 204–205: distinct closed cubes at one
    level meet only in coordinate hyperplanes. This is the geometric reason
    the hyperplane-null reduction permits finite additivity. Source context:
    DyadicCubeGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric DyadicCubeGridUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dyadic_cube_distinct_overlap_hyperplane]:
    supporting boundary observation for 2.10.47(1),
    pp. 204–205. One separating coordinate is enough;
    the intersection may also be empty. In dimension
    zero distinct indices do not exist. *)
Theorem dyadic_cube_distinct_overlap_hyperplane (R : realType) n (a : R_n R n)
    Q : is_dyadic_cube_grid a Q -> forall j s t, s != t ->
  exists (i : 'I_n) (b : R),
    (@Q j s `&` @Q j t) `<=` [set x | x i=b].
Proof.
move=> hQ j s t hst.
have [i hi] : exists i, s i != t i.
  apply: contrapT=> hh; apply: (elimN eqP hst); apply/ffunP=> i.
  case: (eqVneq (s i) (t i))=> [he|hne]; first exact he.
  exfalso; apply: hh; by exists i.
have hval : (s i : nat) != (t i : nat).
  apply/eqP=> he; apply: (elimN eqP hi); exact: val_inj he.
have hd : (0 : R)<=((2^j)%N)%:R^-1 by rewrite invr_ge0 ler0n.
case: (ltngtP (s i : nat) (t i : nat))=> [hlt|hgt|heq].
- exists i, (a i+((s i).+1)%:R/((2^j)%N)%:R)=> x [hs ht].
  have /andP [hsl hsu] := (proj1 (@hQ j s x) hs) i.
  have /andP [htl htu] := (proj1 (@hQ j t x) ht) i.
  have hsep : (((s i).+1)%:R : R)/((2^j)%N)%:R<=(t i)%:R/((2^j)%N)%:R.
    apply: ler_wpM2r; first exact hd.
    by rewrite ler_nat.
  apply/eqP; rewrite eq_le; apply/andP; split; lra.
- exists i, (a i+(s i)%:R/((2^j)%N)%:R)=> x [hs ht].
  have /andP [hsl hsu] := (proj1 (@hQ j s x) hs) i.
  have /andP [htl htu] := (proj1 (@hQ j t x) ht) i.
  have hsep : (((t i).+1)%:R : R)/((2^j)%N)%:R<=(s i)%:R/((2^j)%N)%:R.
    apply: ler_wpM2r; first exact hd.
    by rewrite ler_nat.
  apply/eqP; rewrite eq_le; apply/andP; split; lra.
- by move: hval; rewrite heq eqxx.
Qed.
