(** Federer (1969), 3.1.11, p. 219:
    the finite norm of a continuous symmetric
    multilinear map agrees with the symmetric-form
    operator norm already specified in 1.10.5,
    p. 47. The target norm follows the
    erratum, p. 4, book p. 219 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  SymmetricForms SymmetricOperatorNormUP SymmetricOperatorNorm SymmetricOperatorTupleBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_symmetric_norm]:
    the Chapter 3 continuous-form norm is the
    finite case of the Chapter 1 symmetric-form
    norm, Federer 3.1.11, p. 219,
    and 1.10.5, p. 47. The equality
    includes degree zero and zero-dimensional spaces. *)
Theorem continuous_multilinear_symmetric_norm (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (ev : {ffun 'I_k->X}->Hom Z Y) (ZN : Z->R)
    (hZ : is_continuous_multilinear_space NX NY ev ZN)
    (z : Z) (phi : S_m X Y k) :
  (forall t, phi t=ev [ffun i=>tnth t i] z) ->
  symmetric_operator_norm hNX.1 NY phi=(ZN z)%:E.
Proof.
move=> he.
pose op := symmetric_operator_norm hNX.1 NY phi.
have hn := multilinear_operator_nonnegative (continuous_multilinear_norm_laws hZ z).
have hupper : (op<=(ZN z)%:E)%E.
  apply: (symmetric_operator_norm_bound hNX.1 NY phi (ZN z)).2=>t ht.
  rewrite he.
  have hb := multilinear_operator_bound (continuous_multilinear_norm_laws hZ z)
    [ffun i=>tnth t i].
  have hprod : \prod_(i<k) NX (tnth t i)<= 1.
    have hterms i (_ : predT i) : 0<=NX (tnth t i)<= 1.
      apply/andP; split; [exact (real_seminorm_nonnegative hNX.1 (tnth t i))|exact: ht i].
    have hh := @ler_prod R 'I_k (Finite.enum 'I_k) predT
      (fun i=>NX (tnth t i)) (fun _=>1) hterms.
    change (is_true (\prod_(i<k) NX (tnth t i)<=\prod_(i<k) (1:R))) in hh.
    have hone : (\prod_(i<k) (1:R))= 1 by apply: big1.
    by rewrite hone in hh.
  have hp : \prod_(i<k) NX ([ffun j=>tnth t j] i)<= 1.
    have hh : (\prod_(i<k) NX ([ffun j=>tnth t j] i))=
        \prod_(i<k) NX (tnth t i).
      apply: eq_bigr=>i _; by rewrite ffunE.
    by rewrite hh.
  have hs := ler_wpM2l hn hp; rewrite mulr1 in hs.
  exact: le_trans hb hs.
have hnonneg : (0<=op)%E := symmetric_operator_norm_ge_zero hNX.1 hNY.1 phi.
have hfinite : op \is a fin_num.
  rewrite (ge0_fin_numE hnonneg); exact: le_lt_trans hupper (ltry _).
pose c := fine op.
have hop : op=c%:E by rewrite /c fineK.
have hc : 0<=c by move: hnonneg; rewrite hop lee_fin.
have hleast : ZN z<=c.
  apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ z) hc)=>u.
  have hle : (op<=c%:E)%E by rewrite hop.
  have hb := @symmetric_operator_finite_tuple_bound R X Y NX NY hNX hNY.1
    k phi c hle [tuple u i | i<k].
  have hu : [ffun i=>tnth [tuple u j | j<k] i]=u.
    by apply/ffunP=>i; rewrite ffunE tnth_mktuple.
  rewrite he hu in hb.
  have hp : (\prod_(i<k) NX (tnth [tuple u j | j<k] i))=
      \prod_(i<k) NX (u i).
    apply: eq_bigr=>i _; by rewrite tnth_mktuple.
  by rewrite hp in hb.
change (op=(ZN z)%:E).
rewrite hop; congr (_%:E).
apply/eqP; rewrite eq_le; apply/andP; split=> //.
by move: hupper; rewrite hop lee_fin.
Qed.
