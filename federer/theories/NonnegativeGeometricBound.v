(** Federer (1969), 3.2.13, p. 250: summable
    geometric costs for the two dyadic parts of the Gamma
    integral. Derive the bound by telescoping finite prefixes
    through the existing abstract nonnegative-sum laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal lra ring.
From Federer Require Import NonnegativeSum NonnegativeSumNatPrefix NonnegativeSeriesParity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_geometric_bound]: the
    summable dyadic majorants establishing the Gamma integral
    in Federer 3.2.13, p. 250. Zero
    coefficient and zero ratio are retained. *)
Lemma nonnegative_geometric_bound (R:realType) (C q:R):
  (0<= C)%R ->(0<=q)%R ->(q<1)%R ->
  nonnegative_sum setT (fun n=>(C*q^+n)%R%:E)<=(C/(1-q))%R%:E.
Proof.
move=>hC hq hq1.
pose A:=(C/(1-q))%R.
have hDen:(0<1-q)%R by lra.
have hDenNe:(1-q!=0)%R:=lt0r_neq0 hDen.
have hA:(0<=A)%R by apply:divr_ge0=> //; exact:ltW hDen.
have hCancel:(A*(1-q) = C)%R by rewrite /A divfK.
have hTail n:(0<=A*q^+n)%R:=mulr_ge0 hA (exprn_ge0 n hq).
have hCost n:0<=(C*q^+n)%R%:E by rewrite lee_fin; exact:mulr_ge0 hC (exprn_ge0 n hq).
have hStep n:(C*q^+n=A*q^+n-A*q^+n.+1)%R.
  have hFactor:(A*q^+n-A*q^+n.+1=A*(1-q)*q^+n)%R by rewrite exprS; ring.
  by rewrite hFactor hCancel.
have hPrefix N:nonnegative_sum [set n|(n<N)%N] (fun n=>(C*q^+n)%R%:E)=
    (A-A*q^+N)%R%:E.
  elim:N=>[|N ih].
  - by rewrite nonnegative_sum_nat_prefix_zero expr0 mulr1 subrr.
  - rewrite (nonnegative_sum_nat_prefix_succ N hCost) ih -EFinD.
    congr (_%:E); rewrite hStep; ring.
apply:nonnegative_series_prefix_bound=>N.
rewrite hPrefix lee_fin lerBlDr lerDl; exact:hTail.
Qed.
