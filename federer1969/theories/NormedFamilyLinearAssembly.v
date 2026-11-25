(** Federer (1969), 3.1.1(4), p. 210, and
    3.1.11, pp. 219–220: bounded linear maps into an
    abstract finite normed product are determined by their
    coordinates. This supports diagonal polynomial maps.
    Only the product laws are used in the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormedFamilyUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_family_linear_assembly]: supporting
    assembly of coordinate maps in the finite product of
    Federer 3.1.1(4), p. 210. The coordinate
    bounds sum to a bound in the specified product norm. *)
Theorem normed_family_linear_assembly (R : realType) k
    (X : lmodType R) (V : 'I_k->lmodType R) (P : lmodType R)
    (NX : X->R) (N : forall i, V i->R)
    (coordinate : forall i, Hom P (V i)) (PN : P->R)
    (hP : is_normed_family N coordinate PN)
    (T : forall i, Hom X (V i)) :
  (forall i, norm_bounded_linear NX (N i) (T i)) ->
  exists D : Hom X P,
    (forall x i, coordinate i (D x)=T i x) /\
    norm_bounded_linear NX PN D.
Proof.
move=> hT.
have hex x : exists u : P, forall i, coordinate i u=T i x.
  have [u hu] := normed_family_surjective hP [ffun i : 'I_k=>T i x].
  exists u=> i; by rewrite hu ffunE.
have [d hd] := choice hex.
have hlin : linear d.
  move=> c x y; apply: (normed_family_extensional hP)=> i.
  by rewrite hd (hom_linear (coordinate i)) !hd (hom_linear (T i)).
pose D := @HomMap R X P d (introT (asboolP _) hlin).
exists D; split; first exact hd.
have [C hC] := choice hT.
exists (\sum_(i<k) C i); split.
- apply: sumr_ge0=> i _; exact: (hC i).1.
- move=> x; rewrite (normed_family_norm hP) mulr_suml.
  apply: ler_sum=> i _; change (N i (coordinate i (d x))<=C i*NX x).
  rewrite hd; exact: (hC i).2.
Qed.

(** Source for [normed_family_diagonal_exists]: the
    repeated-variable map used to evaluate multilinear
    forms as polynomials in Federer 3.1.11, p. 220.
    It exists in any product satisfying the abstract laws,
    including the product of zero factors. *)
Theorem normed_family_diagonal_exists (R : realType) k
    (X P : lmodType R) (NX : X->R)
    (coordinate : forall i : 'I_k, Hom P X) (PN : P->R)
    (hP : is_normed_family (fun _ : 'I_k=>NX) coordinate PN) :
  exists D : Hom X P,
    (forall x i, coordinate i (D x)=x) /\
    (forall x, PN (D x)=k%:R*NX x) /\
    norm_bounded_linear NX PN D.
Proof.
have hid : linear (fun x : X=>x) by move=> c x y.
pose Id := @HomMap R X X (fun x=>x) (introT (asboolP _) hid).
have hb (i : 'I_k) : norm_bounded_linear NX NX Id.
  exists 1; split; first exact: ler01.
  by move=> x; rewrite mul1r.
have [D [hD hDb]] := @normed_family_linear_assembly R k X
  (fun _ : 'I_k=>X) P NX (fun _=>NX) coordinate PN hP (fun _=>Id) hb.
exists D; split; first exact hD.
split=> // x.
rewrite (normed_family_norm hP).
under eq_bigr do rewrite hD.
by rewrite sumr_const card_ord /Id /= mulr_natl.
Qed.
